(** MCP (Model Context Protocol) server — the agents-first surface.

    JSON-RPC 2.0 over stdio, one JSON object per line (the MCP stdio
    transport). Serves `initialize` / `tools/list` / `tools/call` /
    `ping`; capabilities declare tools only.

    Tools multiplex NAMED proof sessions (label → [Ec_llm_session]):
    parallel subagents each hold a coherent EC state by using their
    own session label, which is the mechanism behind
    parallel-per-lemma dispatch (doc/ecllm-compat.md agenda §9).
    Sessions carry an EDIT MODE making the read-only-prefix
    discipline enforced rather than conventional: statement-mode
    (may change declarations) is exclusive per file; proof-mode
    sessions parallelize but must claim their target lemmas, and
    overlapping claims are refused. Every tool result is a JSON
    payload serialized into a single text content block, so agents
    parse rather than scrape.

    v1 scope notes:
    - Session bootstrap is [open_file] (EcLlm's LOAD under the hood,
      with `-nosmt` weak-check available for fast prefixes).
    - [try_tactic] is capture → exec → goals → revert-to-uuid on the
      labeled session; the session's real state is never left moved.
    - No server-initiated messages, no resources/prompts, no
      cancellation (EcCancel is deferred from pass 1). *)

let server_version = "0.1.0"

(* ---------------------------------------------------------------- *)
(* Server state                                                       *)
(* ---------------------------------------------------------------- *)

(* A proof-mode session's claim on one lemma, with the document
   region it resolves to (declaration through its closing qed/save,
   or through the last sentence before the next declaration when the
   proof is unfinished). Regions are informational for the
   orchestrator's splicing; the LOCK KEY is the lemma name. *)
type claim = {
  lemma         : string;
  start_line    : int;
  decl_end_line : int;  (* last line of the declaration sentence *)
  end_line      : int;
}

(* Edit mode declared at open_file:
   - [Statement]: may change declarations — requires EXCLUSIVE access
     to the file (no other session, of either mode).
   - [Proof cs]: edits proof bodies only — parallelizes freely, but
     must claim its target lemmas; overlapping claims are refused.
   Locks are derived from the live session table (no separate
   registry to desync): closing or replacing a session releases its
   locks. Cross-FILE dependencies are not modeled in v1 — a
   statement session on a required file does not block dependents.

   Pinned v2 (doc/ecllm-compat.md "Edit-mode roadmap"): proof claims
   refine to per-SUBGOAL, bullet-driven under +strict_bullets with
   proof-tree verification; statement splits into full (exclusive)
   vs additive (parallel, insert-only, semantic no-shadowing
   guard). *)
type mode =
  | Statement
  | Proof of claim list

let is_statement = function Statement -> true | Proof _ -> false
let mode_label = function Statement -> "statement" | Proof _ -> "proof"
let claim_names = function
  | Statement -> []
  | Proof cs -> List.map (fun c -> c.lemma) cs

(* "Semantic bullets": a live per-subgoal claim on a session. The
   agent works one claimed subtree at a time; containment is
   enforced semantically (goal-count accounting + a lexical gate on
   focus-moving tactics), not by textual bullets — COMMIT re-emits
   bullets on the way back to text. One active subclaim per session:
   true intra-proof parallelism = one worker session per subgoal. *)
type subclaim = {
  sc_path : string;
  sc_entry_hash : string;
  mutable sc_remaining : int;
  mutable sc_transcript : string list;  (* reversed *)
  mutable sc_closed : bool;
}

type entry = {
  session : Ec_llm_session.t;
  file    : string;   (* canonical path — the lock-pool key *)
  mutable mode   : mode;
  (* Snapshot of the file as last loaded/synced: the resync diff
     baseline and the staleness reference. *)
  mutable text   : string;
  mutable hash   : Digest.t;
  mutable parsed : Ec_llm_session.parsed_sentence array;
  (* Leading file-sentence count the session state equals, or -1
     once interactive work diverged (resync fast-forward gate). *)
  mutable synced_upto : int;
  mutable subclaim : subclaim option;
}

type t = {
  sw       : Eio.Switch.t;
  sessions : (string, entry) Hashtbl.t;
}

let default_label = "main"

let label_of_args args =
  match Yojson.Safe.Util.member "session" args with
  | `String s when s <> "" -> s
  | _ -> default_label

let find_session t args =
  let label = label_of_args args in
  match Hashtbl.find_opt t.sessions label with
  | Some e -> Ok (label, e)
  | None ->
    Error
      (Printf.sprintf
         "no session '%s' — call open_file first (optionally with a \
          {\"session\": \"<label>\"} argument to run parallel \
          sessions)" label)

(* ---------------------------------------------------------------- *)
(* Small JSON helpers                                                 *)
(* ---------------------------------------------------------------- *)

let str_arg args name =
  match Yojson.Safe.Util.member name args with
  | `String s -> Some s
  | _ -> None

let int_arg args name =
  match Yojson.Safe.Util.member name args with
  | `Int n -> Some n
  | _ -> None

let bool_arg args name =
  match Yojson.Safe.Util.member name args with
  | `Bool b -> b
  | _ -> false

(* Best-effort embed: parse [s] as JSON so the payload nests
   structurally; fall back to the raw string. *)
let json_or_string s =
  try Yojson.Safe.from_string s with _ -> `String s

let goals_json session : Yojson.Safe.t =
  match Ec_llm_session.goals ~structured:true session with
  | Error e -> `Assoc [ "error", `String (Error.to_string e) ]
  | Ok raw -> json_or_string raw

(* ---------------------------------------------------------------- *)
(* Tool implementations                                               *)
(* ---------------------------------------------------------------- *)

(* Each handler: t -> arguments -> (payload, error-text) result. *)

let absolute path =
  if Filename.is_relative path then Filename.concat (Sys.getcwd ()) path
  else path

(* Canonical path = the lock-pool key; realpath collapses spelling
   variants so two sessions can't dodge each other's locks. *)
let canonical path =
  let p = absolute path in
  try Unix.realpath p with _ -> p

let str_list_arg args name =
  match Yojson.Safe.Util.member name args with
  | `List xs ->
    Some
      (List.filter_map
         (function `String s when s <> "" -> Some s | _ -> None)
         xs)
  | _ -> None

let read_file path =
  let ic = open_in_bin path in
  let n = in_channel_length ic in
  let s = really_input_string ic n in
  close_in ic;
  s

let write_file path text =
  let oc = open_out_bin path in
  output_string oc text;
  close_out oc

(* Stale = the on-disk file no longer matches what this session
   loaded/synced. Surfaced on state-bearing replies so a
   refactoring loop can't silently trust a result computed against
   old text. *)
let stale_flag (e : entry) =
  match Digest.file e.file with
  | d -> d <> e.hash
  | exception _ -> true

let ms_since t0 =
  int_of_float ((Unix.gettimeofday () -. t0) *. 1000.)

let sentence_class_of (s : Ec_llm_session.parsed_sentence) =
  match s.cls with
  | `Executable -> Some `Executable
  | `Directive -> Some `Directive
  | `Doc_comment -> Some `Doc_comment
  | `Meta -> None

(* True when the session has no open goal (proof closed or no active
   proof) — the `closes` verdict for candidate scripts. *)
let goals_closed session =
  match Ec_llm_session.goals ~structured:true session with
  | Error _ -> false
  | Ok raw ->
    (match Yojson.Safe.from_string raw with
     | exception _ -> false
     | j ->
       (match Yojson.Safe.Util.member "active" j with
        | `Bool false -> true
        | _ ->
          (match Yojson.Safe.Util.member "subgoal_count" j with
           | `Int 0 -> true
           | _ -> false)))

(* (open-goal count, subgoal JSON list) at the current state. *)
let goals_info session =
  match Ec_llm_session.goals ~structured:true session with
  | Error _ -> (0, [])
  | Ok raw ->
    (match Yojson.Safe.from_string raw with
     | exception _ -> (0, [])
     | j ->
       let open Yojson.Safe.Util in
       let n =
         match member "subgoal_count" j with `Int n -> n | _ -> 0
       in
       let subs =
         match member "subgoals" j with `List l -> l | _ -> []
       in
       (n, subs))

(* Obligation identity of one subgoal: hash of (hypotheses,
   conclusion) — position-independent, so before/after outlines can
   be diffed by hash ("same debt, reorganized" vs changed). *)
let subgoal_hash sub =
  let open Yojson.Safe.Util in
  let h = member "hypotheses" sub in
  let c = member "conclusion" sub in
  Digest.to_hex
    (Digest.string (Yojson.Safe.to_string (`List [ h; c ])))

let one_line_concl sub =
  let open Yojson.Safe.Util in
  let rec flat j =
    match member "kind" j with
    | `String "pp" ->
      (match member "text" j with `String s -> s | _ -> "")
    | `String k -> "<" ^ k ^ ">"
    | _ -> ""
  in
  let s = flat (member "conclusion" sub) in
  let s = String.map (function '\n' -> ' ' | c -> c) s in
  if String.length s > 80 then String.sub s 0 79 ^ "…" else s

(* Leaf paths from a TREE reply: lines shaped "[1.2] <goal> ...". *)
let tree_paths body =
  String.split_on_char '\n' body
  |> List.filter_map (fun line ->
      let line = String.trim line in
      if String.length line > 2 && line.[0] = '[' then
        match String.index_opt line ']' with
        | Some i -> Some (String.sub line 1 (i - 1))
        | None -> None
      else None)

let first_token s =
  let s = String.trim s in
  let n = String.length s in
  let rec go i = if i < n && s.[i] <> ' ' && s.[i] <> '\n' then go (i+1) else i in
  let k = go 0 in
  String.sub s 0 k

(* DFS frame stack over goal-count deltas: applying a sentence to
   the focused goal replaces it with c = delta+1 children (0 =
   closed leaf, 1 = continuation, >=2 = split). Reconstructs branch
   paths with no proof-DAG wire access. *)
module Frame_stack = struct
  type t = (int * int) list ref  (* (current child, total), innermost first *)

  let make () : t = ref []

  let path (st : t) =
    match !st with
    | [] -> ""
    | fs -> String.concat "." (List.rev_map (fun (c, _) -> string_of_int c) fs)

  let rec bump = function
    | [] -> []
    | (c, total) :: rest ->
      if c < total then (c + 1, total) :: rest else bump rest

  (* Apply one sentence's child count; returns `Split when it opened
     a split point. *)
  let apply (st : t) ~children =
    if children = 0 then begin st := bump !st; `Closed end
    else if children = 1 then `Cont
    else begin st := (1, children) :: !st; `Split end
end

(* ---------------------------------------------------------------- *)
(* Lemma-claim resolution (proof mode)                                *)
(* ---------------------------------------------------------------- *)

let ident_prefix s =
  let is_id c =
    (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')
    || (c >= '0' && c <= '9') || c = '_' || c = '\''
  in
  let n = String.length s in
  let rec go i = if i < n && is_id s.[i] then go (i + 1) else i in
  let k = go 0 in
  if k = 0 then None else Some (String.sub s 0 k)

(* EC attaches leading comments to the following sentence, so a
   declaration's src may begin with one or more banner `(* ... *)`
   blocks (house style on real codebases — field report
   2026-07-26). Strip them, nesting-aware, before tokenizing. *)
let strip_leading_comments (src : string) : string =
  let n = String.length src in
  let rec skip_ws i =
    if i < n
       && (src.[i] = ' ' || src.[i] = '\t' || src.[i] = '\n'
           || src.[i] = '\r')
    then skip_ws (i + 1)
    else i
  in
  let rec skip_comment i depth =
    if i + 1 >= n then n
    else if src.[i] = '(' && src.[i + 1] = '*' then
      skip_comment (i + 2) (depth + 1)
    else if src.[i] = '*' && src.[i + 1] = ')' then
      if depth = 1 then i + 2 else skip_comment (i + 2) (depth - 1)
    else skip_comment (i + 1) depth
  in
  let rec go i =
    let i = skip_ws i in
    if i + 1 < n && src.[i] = '(' && src.[i + 1] = '*' then
      go (skip_comment (i + 2) 1)
    else i
  in
  let k = go 0 in
  if k >= n then "" else String.sub src k (n - k)

(* Extract the declared name from a proof-opening declaration's
   SOURCE text (not pp output): strip attached leading comments,
   skip local/declare prefixes and nosmt / [attribute] tokens after
   the keyword; the name is the leading identifier of the next
   token. v1 heuristic — validation errors list every declaration
   found, so mismatches are visible. *)
let decl_name (src : string) : string option =
  let src = strip_leading_comments src in
  let toks =
    String.split_on_char '\n' src
    |> List.concat_map (String.split_on_char '\t')
    |> List.concat_map (String.split_on_char ' ')
    |> List.filter (fun s -> s <> "")
  in
  let rec after_kw = function
    | [] -> None
    | ("local" | "declare") :: rest -> after_kw rest
    | ("lemma" | "axiom") :: rest -> skip_attrs rest
    | _ -> None
  and skip_attrs = function
    | [] -> None
    | "nosmt" :: rest -> skip_attrs rest
    | tok :: rest when String.length tok > 0 && tok.[0] = '[' ->
      skip_attrs rest
    | tok :: _ -> ident_prefix tok
  in
  after_kw toks

(* Resolve claimed lemma names against the file's PARSE-JSON
   sentence list. A claim's region runs from its declaration through
   the closing Gsave (qed/save/abort); an unfinished proof extends
   to the last sentence before the next declaration (or EOF). *)
let resolve_claims
    (sentences : Ec_llm_session.parsed_sentence array)
    (wanted : string list) : (claim list, string) result =
  let decls =
    Array.to_list sentences
    |> List.mapi (fun i s -> (i, s))
    |> List.filter_map
         (fun (i, (s : Ec_llm_session.parsed_sentence)) ->
            if s.kind = "Gaxiom" then
              Option.map (fun n -> (n, i, s)) (decl_name s.src)
            else None)
  in
  let region_of i (decl : Ec_llm_session.parsed_sentence) =
    let n = Array.length sentences in
    let rec scan j last =
      if j >= n then last
      else
        let (sj : Ec_llm_session.parsed_sentence) = sentences.(j) in
        if sj.kind = "Gaxiom" then last
        else if sj.kind = "Gsave" then sj.end_line
        else scan (j + 1) sj.end_line
    in
    (decl.start_line, scan (i + 1) decl.end_line)
  in
  let find name =
    match List.find_opt (fun (n, _, _) -> n = name) decls with
    | Some (n, i, s) ->
      let (a, b) = region_of i s in
      Ok { lemma = n; start_line = a;
           decl_end_line = s.end_line; end_line = b }
    | None ->
      let avail = List.map (fun (n, _, _) -> n) decls in
      let avail =
        if List.length avail > 20 then
          List.filteri (fun i _ -> i < 20) avail @ [ "..." ]
        else avail
      in
      Error
        (Printf.sprintf
           "lemma '%s' not found in file (declarations found: %s)"
           name
           (if avail = [] then "none" else String.concat ", " avail))
  in
  List.fold_left
    (fun acc name ->
       match acc with
       | Error _ as e -> e
       | Ok cs ->
         (match find name with
          | Ok c -> Ok (cs @ [ c ])
          | Error e -> Error e))
    (Ok []) wanted

(* ---------------------------------------------------------------- *)
(* Lock evaluation                                                    *)
(* ---------------------------------------------------------------- *)

let lock_conflicts t ~file ~(mode : mode) ~self_label =
  let holders =
    Hashtbl.fold
      (fun l e acc ->
         if l = self_label || e.file <> file then acc
         else (l, e) :: acc)
      t.sessions []
  in
  if holders = [] then Ok ()
  else
    match mode with
    | Statement ->
      let show (l, e) =
        Printf.sprintf "'%s' (%s%s)" l (mode_label e.mode)
          (match claim_names e.mode with
           | [] -> ""
           | ns -> ": " ^ String.concat ", " ns)
      in
      Error
        (Printf.sprintf
           "statement-mode needs exclusive access to %s — held by %s \
            (close those sessions first)"
           file
           (String.concat ", " (List.map show holders)))
    | Proof cs ->
      (match
         List.find_opt (fun (_, e) -> is_statement e.mode) holders
       with
       | Some (l, _) ->
         Error
           (Printf.sprintf
              "%s is locked by statement-mode session '%s'" file l)
       | None ->
         let mine = List.map (fun c -> c.lemma) cs in
         let taken =
           List.concat_map
             (fun (l, e) ->
                List.filter_map
                  (fun n ->
                     if List.mem n mine then Some (n, l) else None)
                  (claim_names e.mode))
             holders
         in
         (match taken with
          | [] -> Ok ()
          | _ ->
            let show (n, l) =
              Printf.sprintf "%s (held by session '%s')" n l
            in
            Error
              (Printf.sprintf "lemma claim conflict: %s"
                 (String.concat ", " (List.map show taken)))))

let claims_json = function
  | Statement -> `Null
  | Proof cs ->
    `List
      (List.map
         (fun c ->
            `Assoc [
              "lemma", `String c.lemma;
              "start_line", `Int c.start_line;
              "decl_end_line", `Int c.decl_end_line;
              "end_line", `Int c.end_line;
            ])
         cs)

let tool_open_file t args =
  match str_arg args "path" with
  | None -> Error "open_file: missing required argument 'path'"
  | Some path ->
    let path = canonical path in
    if not (Sys.file_exists path) then
      Error (Printf.sprintf "open_file: no such file: %s" path)
    else begin
      let label = label_of_args args in
      let wanted_mode =
        match str_arg args "mode" with
        | None | Some "statement" -> Ok `Statement
        | Some "proof" ->
          (match str_list_arg args "lemmas" with
           | Some (_ :: _ as ls) -> Ok (`Proof ls)
           | Some [] | None ->
             Error
               "open_file: proof mode requires a non-empty 'lemmas' \
                claim list (the lemmas this session will work on)")
        | Some other ->
          Error
            (Printf.sprintf
               "open_file: unknown mode '%s' (statement | proof)"
               other)
      in
      match wanted_mode with
      | Error e -> Error e
      | Ok wanted ->
        (* Replace an existing session under this label — its locks
           release with it (even on a failed re-open). *)
        (match Hashtbl.find_opt t.sessions label with
         | Some e ->
           (try Ec_llm_session.close e.session with _ -> ());
           Hashtbl.remove t.sessions label
         | None -> ());
        (* Evaluate locks BEFORE spawning: claim names suffice for
           conflict detection; regions resolve after parse. *)
        let probe_mode =
          match wanted with
          | `Statement -> Statement
          | `Proof ls ->
            Proof
              (List.map
                 (fun l ->
                    { lemma = l; start_line = 0;
                      decl_end_line = 0; end_line = 0 })
                 ls)
        in
        (match
           lock_conflicts t ~file:path ~mode:probe_mode
             ~self_label:label
         with
         | Error e -> Error e
         | Ok () ->
           let session =
             Ec_llm_session.start_in_dir
               ~cwd:(Filename.dirname path) ~sw:t.sw
               ~label:(Printf.sprintf "mcp-%s" label)
           in
           let fail msg =
             (try Ec_llm_session.close session with _ -> ());
             Error msg
           in
           (* Read + parse the file once (stateless PARSE frame on
              the fresh session): claim resolution, the resync diff
              baseline, and the stale hash all come from this
              snapshot. *)
           (match read_file path with
            | exception Sys_error m ->
              fail (Printf.sprintf "open_file: %s" m)
            | text ->
              (match Ec_llm_session.parse_source session text with
               | Error e ->
                 fail
                   (Printf.sprintf "open_file: parse failed: %s"
                      (Error.to_string e))
               | Ok ss ->
                 let parsed = Array.of_list ss in
                 let resolved_mode =
                   match wanted with
                   | `Statement -> Ok Statement
                   | `Proof ls ->
                     (match resolve_claims parsed ls with
                      | Error e -> Error ("open_file: " ^ e)
                      | Ok cs -> Ok (Proof cs))
                 in
                 (match resolved_mode with
                  | Error e -> fail e
                  | Ok mode ->
                    let load_cmd =
                      let upto =
                        match int_arg args "upto_line" with
                        | Some n -> Printf.sprintf " %d" n
                        | None -> ""
                      in
                      let nosmt =
                        if bool_arg args "nosmt" then " -nosmt" else ""
                      in
                      Printf.sprintf "LOAD \"%s\"%s%s" path upto nosmt
                    in
                    let t0 = Unix.gettimeofday () in
                    (match
                       Ec_llm_session.raw_command session load_cmd
                     with
                     | Error e ->
                       fail
                         (Printf.sprintf "open_file: LOAD failed: %s"
                            (Error.to_string e))
                     | Ok (body, _notices) ->
                       let synced0 =
                         match int_arg args "upto_line" with
                         | None -> Array.length parsed
                         | Some l ->
                           let c = ref 0 in
                           Array.iteri
                             (fun i
                               (s : Ec_llm_session.parsed_sentence) ->
                                if s.end_line <= l then c := i + 1)
                             parsed;
                           !c
                       in
                       Hashtbl.replace t.sessions label
                         { session; file = path; mode; text;
                           hash = Digest.string text; parsed;
                           synced_upto = synced0;
                           subclaim = None };
                       Ok (`Assoc [
                         "session", `String label;
                         "file", `String path;
                         "mode", `String (mode_label mode);
                         "claims", claims_json mode;
                         "uuid",
                         `Int (Ec_llm_session.current_uuid session);
                         "load_time_ms", `Int (ms_since t0);
                         "load_output", `String body;
                         "goals", goals_json session;
                       ]))))))
    end

let tool_exec t args =
  match str_arg args "text" with
  | None -> Error "exec: missing required argument 'text'"
  | Some text ->
    (match find_session t args with
     | Error e -> Error e
     | Ok (label, e) ->
       let corr = Correlation.of_client "mcp-exec" in
       let t0 = Unix.gettimeofday () in
       (match
          Ec_llm_session.exec e.session ~corr
            ~sentence_class:`Executable ~source:text
        with
        | Error err -> Error (Error.to_string err)
        | Ok ok ->
          e.synced_upto <- -1;
          Ok (`Assoc [
            "session", `String label;
            "uuid", `Int ok.replied_uuid;
            "restarted", `Bool ok.restarted;
            "time_ms", `Int (ms_since t0);
            "stale", `Bool (stale_flag e);
            "notices", `List (List.map (fun n -> `String n) ok.notices);
            "goals", goals_json e.session;
          ])))

let tool_query t args =
  match str_arg args "text" with
  | None -> Error "query: missing required argument 'text'"
  | Some text ->
    (match find_session t args with
     | Error e -> Error e
     | Ok (label, e) ->
       let corr = Correlation.of_client "mcp-query" in
       (match
          Ec_llm_session.exec e.session ~corr
            ~sentence_class:`Directive ~source:text
        with
        | Error err -> Error (Error.to_string err)
        | Ok ok ->
          let output =
            String.concat "\n"
              (ok.notices @ (if ok.output = "" then [] else [ ok.output ]))
          in
          Ok (`Assoc [
            "session", `String label;
            "output", `String output;
          ])))

let tool_search t args =
  match str_arg args "pattern" with
  | None -> Error "search: missing required argument 'pattern'"
  | Some pattern ->
    (match find_session t args with
     | Error e -> Error e
     | Ok (label, e) ->
       let strict = bool_arg args "strict" in
       let verb = if strict then "search" else "searchall" in
       let pattern =
         let p = String.trim pattern in
         if String.length p > 0 && p.[String.length p - 1] = '.'
         then String.sub p 0 (String.length p - 1)
         else p
       in
       let limit =
         match int_arg args "limit" with
         | Some n when n > 0 -> n
         | _ -> 50
       in
       let source = Printf.sprintf "%s %s." verb pattern in
       let corr = Correlation.of_client "mcp-search" in
       (match
          Ec_llm_session.exec e.session ~corr
            ~sentence_class:`Directive ~source
        with
        | Error err -> Error (Error.to_string err)
        | Ok ok ->
          let hits = Search_result.of_notices ok.notices in
          let total = List.length hits in
          let shown = List.filteri (fun i _ -> i < limit) hits in
          Ok (`Assoc [
            "session", `String label;
            "mode", `String verb;
            "total_hits", `Int total;
            "truncated", `Bool (total > limit);
            "hits",
            `List
              (List.map
                 (fun (h : Search_result.hit) ->
                    `Assoc [
                      "qname", `String h.qname;
                      "kind", `String h.kind;
                      "short_name", `String h.short_name;
                      "signature", `String h.signature;
                    ])
                 shown);
          ])))

let tool_goals t args =
  match find_session t args with
  | Error e -> Error e
  | Ok (label, e) ->
    Ok (`Assoc [
      "session", `String label;
      "uuid", `Int (Ec_llm_session.current_uuid e.session);
      "stale", `Bool (stale_flag e);
      "goals", goals_json e.session;
    ])

let tool_tree t args =
  match find_session t args with
  | Error e -> Error e
  | Ok (label, e) ->
    (match Ec_llm_session.raw_command e.session "TREE" with
     | Error err -> Error (Error.to_string err)
     | Ok (body, _) ->
       Ok (`Assoc [ "session", `String label; "tree", `String body ]))

let tool_focus t args =
  match find_session t args with
  | Error e -> Error e
  | Ok (label, e) ->
    let cmd =
      match str_arg args "path" with
      | None | Some "" | Some "next" -> "NEXT"
      | Some p -> "FOCUS " ^ p
    in
    (match Ec_llm_session.raw_command e.session cmd with
     | Error err -> Error (Error.to_string err)
     | Ok (_, _) ->
       e.synced_upto <- -1;
       Ok (`Assoc [
         "session", `String label;
         "uuid", `Int (Ec_llm_session.current_uuid e.session);
         "goals", goals_json e.session;
       ]))

let tool_try_tactic t args =
  match str_arg args "tactic" with
  | None -> Error "try_tactic: missing required argument 'tactic'"
  | Some tactic ->
    (match find_session t args with
     | Error e -> Error e
     | Ok (label, e) ->
       let pre = Ec_llm_session.current_uuid e.session in
       let corr = Correlation.of_client "mcp-try" in
       let t0 = Unix.gettimeofday () in
       (match
          Ec_llm_session.exec e.session ~corr
            ~sentence_class:`Executable ~source:tactic
        with
        | Error err ->
          (* A failed tactic leaves uuid unmoved; nothing to revert. *)
          Ok (`Assoc [
            "session", `String label;
            "outcome", `String "err";
            "error", `String (Error.to_string err);
          ])
        | Ok _ ->
          let goals_after = goals_json e.session in
          (match
             Ec_llm_session.revert_to_uuid e.session ~target:pre
           with
           | Ok () ->
             Ok (`Assoc [
               "session", `String label;
               "outcome", `String "ok";
               "time_ms", `Int (ms_since t0);
               "goals_after", goals_after;
               "reverted_to", `Int pre;
             ])
           | Error err ->
             (* State is now past the candidate — surface loudly. *)
             Error
               (Printf.sprintf
                  "try_tactic: candidate applied but revert failed \
                   (%s); session '%s' state has ADVANCED"
                  (Error.to_string err) label))))

let tool_revert t args =
  match int_arg args "uuid" with
  | None -> Error "revert: missing required argument 'uuid' (int)"
  | Some target ->
    (match find_session t args with
     | Error e -> Error e
     | Ok (label, e) ->
       (match Ec_llm_session.revert_to_uuid e.session ~target with
        | Error err -> Error (Error.to_string err)
        | Ok () ->
          e.synced_upto <- -1;
          Ok (`Assoc [
            "session", `String label;
            "uuid", `Int (Ec_llm_session.current_uuid e.session);
            "goals", goals_json e.session;
          ])))

let tool_commit_proof t args =
  match find_session t args with
  | Error e -> Error e
  | Ok (label, e) ->
    (match Ec_llm_session.raw_command e.session "COMMIT" with
     | Error err -> Error (Error.to_string err)
     | Ok (body, _) ->
       Ok (`Assoc [
         "session", `String label;
         "stale", `Bool (stale_flag e);
         "proof", `String body;
       ]))

let tool_analyze_file t args =
  match str_arg args "path" with
  | None -> Error "analyze_file: missing required argument 'path'"
  | Some path ->
    let path = absolute path in
    let run session =
      let cmd = Printf.sprintf "ANALYZE-JSON \"%s\"" path in
      match Ec_llm_session.raw_command session cmd with
      | Error err -> Error (Error.to_string err)
      | Ok (body, _) ->
        Ok [ "file", `String path; "analysis", json_or_string body ]
    in
    let label = label_of_args args in
    (match Hashtbl.find_opt t.sessions label with
     | Some e ->
       (match run e.session with
        | Error m -> Error m
        | Ok kv -> Ok (`Assoc (("session", `String label) :: kv)))
     | None ->
       (* Stateless as documented: no session needed — spawn an
          ephemeral one so analyze_file stays reachable when
          open_file itself is what failed (field report). *)
       let session =
         Ec_llm_session.start_in_dir
           ~cwd:(Filename.dirname path) ~sw:t.sw ~label:"mcp-analyze"
       in
       let r = run session in
       (try Ec_llm_session.close session with _ -> ());
       (match r with
        | Error m -> Error m
        | Ok kv ->
          Ok (`Assoc (("session", `String "(ephemeral)") :: kv))))

let tool_list_sessions t _args =
  let rows =
    Hashtbl.fold
      (fun label e acc ->
         `Assoc [
           "session", `String label;
           "file", `String e.file;
           "mode", `String (mode_label e.mode);
           "claims", claims_json e.mode;
           "uuid", `Int (Ec_llm_session.current_uuid e.session);
         ] :: acc)
      t.sessions []
  in
  Ok (`Assoc [ "sessions", `List rows ])

let tool_close_session t args =
  let label = label_of_args args in
  match Hashtbl.find_opt t.sessions label with
  | None -> Error (Printf.sprintf "close_session: no session '%s'" label)
  | Some e ->
    (try Ec_llm_session.close e.session with _ -> ());
    Hashtbl.remove t.sessions label;
    Ok (`Assoc [ "closed", `String label ])

(* ---------------------------------------------------------------- *)
(* Refactoring loop: check_script / resync_file / replace_proof       *)
(* ---------------------------------------------------------------- *)

(* Speculatively run a multi-sentence candidate (a whole proof body)
   from the CURRENT state: execute sentence-by-sentence until the
   first failure, report per-sentence verdicts + timing + whether
   the proof closes, then revert to the starting uuid. The session
   is left where it was. *)
let tool_check_script t args =
  match str_arg args "script" with
  | None -> Error "check_script: missing required argument 'script'"
  | Some script ->
    (match find_session t args with
     | Error e -> Error e
     | Ok (label, e) ->
       (match Ec_llm_session.parse_source e.session script with
        | Error err ->
          Error
            (Printf.sprintf "check_script: script parse failed: %s"
               (Error.to_string err))
        | Ok ss ->
          let start = Ec_llm_session.current_uuid e.session in
          let corr = Correlation.of_client "mcp-check" in
          let results = ref [] in
          let failed = ref false in
          let goals_fail = ref `Null in
          let restarted = ref false in
          let t0 = Unix.gettimeofday () in
          (try
             List.iteri
               (fun i (s : Ec_llm_session.parsed_sentence) ->
                  match sentence_class_of s with
                  | None -> ()
                  | Some cls ->
                    let s0 = Unix.gettimeofday () in
                    (match
                       Ec_llm_session.exec e.session ~corr
                         ~sentence_class:cls ~source:s.src
                     with
                     | Ok ok ->
                       if ok.restarted then begin
                         restarted := true;
                         raise Exit
                       end;
                       results :=
                         `Assoc [
                           "index", `Int i;
                           "src", `String s.src;
                           "ok", `Bool true;
                           "uuid", `Int ok.replied_uuid;
                           "time_ms", `Int (ms_since s0);
                         ] :: !results
                     | Error er ->
                       failed := true;
                       goals_fail := goals_json e.session;
                       results :=
                         `Assoc [
                           "index", `Int i;
                           "src", `String s.src;
                           "ok", `Bool false;
                           "error", `String (Error.to_string er);
                           "time_ms", `Int (ms_since s0);
                         ] :: !results;
                       raise Exit))
               ss
           with Exit -> ());
          let closes =
            (not !failed) && (not !restarted)
            && goals_closed e.session
          in
          let goals_at_end = goals_json e.session in
          let restore =
            if !restarted then
              `String
                "session restarted mid-script — state NOT restored; \
                 run resync_file to recover"
            else if Ec_llm_session.current_uuid e.session = start then
              `String "unmoved"
            else
              (match
                 Ec_llm_session.revert_to_uuid e.session ~target:start
               with
               | Ok () -> `String "restored"
               | Error er ->
                 `String ("RESTORE FAILED: " ^ Error.to_string er))
          in
          Ok (`Assoc [
            "session", `String label;
            "checked", `Int (List.length !results);
            "ok", `Bool ((not !failed) && not !restarted);
            "closes", `Bool closes;
            "results", `List (List.rev !results);
            "goals_at_failure", !goals_fail;
            "goals_at_end", goals_at_end;
            "restore", restore;
            "uuid", `Int (Ec_llm_session.current_uuid e.session);
            "total_time_ms", `Int (ms_since t0);
            "stale", `Bool (stale_flag e);
          ])))

(* Incremental re-sync of a session against its (possibly edited)
   file, with sentence-granular target selection over a
   line-granular LOAD: when several sentences share the last prefix
   line (the `proof. tac. qed.` idiom), `LOAD upto <line>` would
   overshoot into the tail — so the prefix boundary backs off to a
   line break and the same-line cluster replays through the exec
   path (field report B2). Targets: whole file, `upto_line`, or
   `at_lemma` (position just inside the lemma's proof, immune to
   packed lines — field report F1). Fast path (field report F2):
   when the file is unchanged and the session state is a known file
   prefix at or behind the target, execute forward from the current
   state with no reload. The changed/executed tail is always
   full-checked; only the reloaded prefix honors [nosmt]. *)
let resync_impl ~label (e : entry) ~nosmt ~upto_line ~at_lemma =
  match read_file e.file with
  | exception Sys_error m -> Error (Printf.sprintf "resync_file: %s" m)
  | text ->
    let unchanged = Digest.string text = e.hash in
    if unchanged && upto_line = None && at_lemma = None
       && e.synced_upto = Array.length e.parsed
    then
      Ok (`Assoc [
        "session", `String label;
        "changed", `Bool false;
        "stale", `Bool false;
        "uuid", `Int (Ec_llm_session.current_uuid e.session);
      ])
    else
      (match Ec_llm_session.parse_source e.session text with
       | Error err ->
         Error
           (Printf.sprintf "resync_file: parse failed: %s"
              (Error.to_string err))
       | Ok ss ->
         let parsed_all = Array.of_list ss in
         let n_all = Array.length parsed_all in
         (* Target = number of leading sentences the session should
            end up having executed. *)
         let target =
           match at_lemma with
           | Some lemma ->
             (match resolve_claims parsed_all [ lemma ] with
              | Error msg -> Error msg
              | Ok [ c ] ->
                let d = ref (-1) in
                Array.iteri
                  (fun i (s : Ec_llm_session.parsed_sentence) ->
                     if !d = -1 && s.kind = "Gaxiom"
                        && s.start_line = c.start_line
                     then d := i)
                  parsed_all;
                if !d < 0 then
                  Error "internal: declaration not re-found"
                else
                  (* Through the declaration, plus its `proof.` when
                     present — lands on the lemma's opening goal. *)
                  let m = !d + 1 in
                  let m =
                    if m < n_all
                       && first_token
                            (parsed_all.(m)
                             : Ec_llm_session.parsed_sentence)
                              .src
                          = "proof"
                    then m + 1
                    else m
                  in
                  Ok m
              | Ok _ -> Error "internal: claim resolution shape")
           | None ->
             (match upto_line with
              | None -> Ok n_all
              | Some l ->
                let m = ref 0 in
                Array.iteri
                  (fun i (s : Ec_llm_session.parsed_sentence) ->
                     if s.end_line <= l then m := i + 1)
                  parsed_all;
                Ok !m)
         in
         (match target with
          | Error msg -> Error ("resync_file: " ^ msg)
          | Ok m ->
            let old = e.parsed in
            let n_old = Array.length old in
            let k =
              let n = min n_old m in
              let rec go i =
                if i < n
                   && (old.(i) : Ec_llm_session.parsed_sentence).src
                      = (parsed_all.(i)
                         : Ec_llm_session.parsed_sentence)
                          .src
                then go (i + 1)
                else i
              in
              go 0
            in
            (* Classification over the DIFF WINDOW only: trim the
               common suffix so unchanged downstream sentences don't
               pollute a mid-file body edit's classification. *)
            let ks =
              let maxs = min (n_old - k) (n_all - k) in
              let rec go i =
                if i < maxs
                   && (old.(n_old - 1 - i)
                       : Ec_llm_session.parsed_sentence)
                        .src
                      = (parsed_all.(n_all - 1 - i)
                         : Ec_llm_session.parsed_sentence)
                          .src
                then go (i + 1)
                else i
              in
              go 0
            in
            let window arr lo hi =
              let out = ref [] in
              Array.iteri
                (fun i (s : Ec_llm_session.parsed_sentence) ->
                   if i >= lo && i < hi then out := s.kind :: !out)
                arr;
              !out
            in
            let diff_kinds =
              window old k (n_old - ks)
              @ window parsed_all k (n_all - ks)
            in
            let proof_kind kd = kd = "Gtactics" || kd = "Gsave" in
            let classification =
              if unchanged then "reposition"
              else if diff_kinds = [] then "formatting-only"
              else if List.for_all proof_kind diff_kinds then
                "proof-body-only"
              else if k >= n_old then "additive"
              else "statement-changing"
            in
            let warning =
              match e.mode with
              | Proof _ when classification = "statement-changing" ->
                [ "warning",
                  `String
                    "statement-changing edit seen by a PROOF-mode \
                     session — declarations should change through a \
                     statement-mode session" ]
              | _ -> []
            in
            let corr = Correlation.of_client "mcp-resync" in
            let exec_range lo hi =
              let err = ref None in
              let cnt = ref 0 in
              (try
                 for i = lo to hi - 1 do
                   let s : Ec_llm_session.parsed_sentence =
                     parsed_all.(i)
                   in
                   match sentence_class_of s with
                   | None -> ()
                   | Some cls ->
                     (match
                        Ec_llm_session.exec e.session ~corr
                          ~sentence_class:cls ~source:s.src
                      with
                      | Ok _ -> incr cnt
                      | Error er ->
                        err := Some (i, s, er);
                        raise Exit)
                 done
               with Exit -> ());
              (!cnt, !err)
            in
            let fast =
              unchanged && e.synced_upto >= 0 && e.synced_upto <= m
              && k >= e.synced_upto
            in
            let run () =
              if fast then begin
                let t1 = Unix.gettimeofday () in
                let (c, er) = exec_range e.synced_upto m in
                Ok (true, 0, ms_since t1, c, er)
              end
              else begin
                (* Back the prefix boundary off shared end-lines so
                   the line-granular LOAD cannot overshoot past the
                   sentence-granular target (B2). *)
                let j = ref (min k m) in
                while
                  !j > 0 && !j < n_all
                  && (parsed_all.(!j)
                      : Ec_llm_session.parsed_sentence)
                       .end_line
                     = (parsed_all.(!j - 1)
                        : Ec_llm_session.parsed_sentence)
                         .end_line
                do
                  decr j
                done;
                let j = !j in
                let prefix_upto =
                  if j = 0 then 0
                  else
                    (parsed_all.(j - 1)
                     : Ec_llm_session.parsed_sentence)
                      .end_line
                in
                let load_cmd =
                  Printf.sprintf "LOAD \"%s\" %d%s" e.file prefix_upto
                    (if nosmt then " -nosmt" else "")
                in
                let t0 = Unix.gettimeofday () in
                match Ec_llm_session.raw_command e.session load_cmd with
                | Error err ->
                  Error
                    (Printf.sprintf
                       "resync_file: prefix reload failed: %s"
                       (Error.to_string err))
                | Ok _ ->
                  let pms = ms_since t0 in
                  let t1 = Unix.gettimeofday () in
                  let (c, er) = exec_range j m in
                  Ok (false, pms, ms_since t1, c, er)
              end
            in
            (match run () with
             | Error msg -> Error msg
             | Ok (fast_forward, prefix_ms, tail_ms, executed, err_opt) ->
               e.text <- text;
               e.hash <- Digest.string text;
               e.parsed <- parsed_all;
               (* Session position moved — any live subgoal claim is
                  void; the synced position is where execution
                  stopped. *)
               e.subclaim <- None;
               e.synced_upto <-
                 (match err_opt with
                  | None -> m
                  | Some (i, _, _) -> i);
               let claims_warning =
                 match e.mode with
                 | Statement -> []
                 | Proof cs ->
                   let names = List.map (fun c -> c.lemma) cs in
                   (match resolve_claims parsed_all names with
                    | Ok cs' ->
                      e.mode <- Proof cs';
                      []
                    | Error msg ->
                      [ "claims_warning",
                        `String
                          (msg
                           ^ " — previous claim regions kept; locks \
                              still held by name") ])
               in
               let base =
                 [
                   "session", `String label;
                   "changed", `Bool (not unchanged);
                   "classification", `String classification;
                   "fast_forward", `Bool fast_forward;
                   "common_prefix_sentences", `Int k;
                   "target_sentences", `Int m;
                   "tail_executed", `Int executed;
                   "prefix_time_ms", `Int prefix_ms;
                   "tail_time_ms", `Int tail_ms;
                   "uuid",
                   `Int (Ec_llm_session.current_uuid e.session);
                   "stale", `Bool false;
                   "claims", claims_json e.mode;
                   "goals", goals_json e.session;
                 ]
                 @ warning @ claims_warning
               in
               (match err_opt with
                | None -> Ok (`Assoc (base @ [ "ok", `Bool true ]))
                | Some (i, s, er) ->
                  Ok
                    (`Assoc
                       (base
                        @ [
                            "ok", `Bool false;
                            "error", `String (Error.to_string er);
                            "goals_at_failure", goals_json e.session;
                            "failed_sentence",
                            `Assoc [
                              "index", `Int i;
                              "src", `String s.src;
                              "start_line", `Int s.start_line;
                            ];
                          ]))))))
(* ---------------------------------------------------------------- *)
(* Strategy level: outline / profile / skeleton / semantic claims    *)
(* ---------------------------------------------------------------- *)

(* Locate a lemma's declaration index + body sentence indices in the
   parsed snapshot. *)
let body_indices (e : entry) lemma =
  match resolve_claims e.parsed [ lemma ] with
  | Error m -> Error m
  | Ok [ c ] ->
    let decl_idx = ref (-1) in
    Array.iteri
      (fun i (s : Ec_llm_session.parsed_sentence) ->
         if !decl_idx = -1 && s.kind = "Gaxiom"
            && s.start_line = c.start_line
         then decl_idx := i)
      e.parsed;
    if !decl_idx < 0 then Error "internal: declaration not re-found"
    else
      let body = ref [] in
      Array.iteri
        (fun i (s : Ec_llm_session.parsed_sentence) ->
           if i > !decl_idx && s.end_line <= c.end_line then
             body := i :: !body)
        e.parsed;
      Ok (c, List.rev !body)
  | Ok _ -> Error "internal: claim resolution shape"

(* Replay a lemma's body sentence-by-sentence, attributing each
   sentence to its branch via the frame stack and capturing split
   obligations + timings. REPOSITIONS the session: prefix is
   weak-checked to the declaration, and the session is left at the
   lemma's end. Powers proof_outline and proof_profile. *)
let outline_engine (e : entry) lemma =
  match body_indices e lemma with
  | Error m -> Error m
  | Ok (c, body) ->
    let load_cmd =
      Printf.sprintf "LOAD \"%s\" %d -nosmt" e.file c.decl_end_line
    in
    (match Ec_llm_session.raw_command e.session load_cmd with
     | Error err ->
       Error
         (Printf.sprintf "prefix load failed: %s" (Error.to_string err))
     | Ok _ ->
       e.subclaim <- None;
       let corr = Correlation.of_client "mcp-outline" in
       let st = Frame_stack.make () in
       let count = ref (fst (goals_info e.session)) in
       let sentences = ref [] in
       let obligations = ref [] in
       let splits = ref 0 in
       let failed = ref None in
       (try
          List.iter
            (fun i ->
               let s : Ec_llm_session.parsed_sentence = e.parsed.(i) in
               match sentence_class_of s with
               | None -> ()
               | Some cls ->
                 let path_before = Frame_stack.path st in
                 let t0 = Unix.gettimeofday () in
                 (match
                    Ec_llm_session.exec e.session ~corr
                      ~sentence_class:cls ~source:s.src
                  with
                  | Error er ->
                    failed := Some (s, Error.to_string er);
                    raise Exit
                  | Ok _ ->
                    let (n, subs) = goals_info e.session in
                    let children = n - !count + 1 in
                    let shape =
                      if s.kind = "Gsave" then `Cont
                      else Frame_stack.apply st ~children
                    in
                    (if shape = `Split then begin
                       incr splits;
                       List.iteri
                         (fun k sub ->
                            if k < children then
                              obligations :=
                                `Assoc [
                                  "path",
                                  `String
                                    (let p = path_before in
                                     let idx = string_of_int (k + 1) in
                                     if p = "" then idx
                                     else p ^ "." ^ idx);
                                  "hash", `String (subgoal_hash sub);
                                  "goal", `String (one_line_concl sub);
                                ] :: !obligations)
                         subs
                     end);
                    count := n;
                    let tok = first_token s.src in
                    sentences :=
                      `Assoc [
                        "path", `String path_before;
                        "src", `String s.src;
                        "time_ms", `Int (ms_since t0);
                        "goals_after", `Int n;
                        "closer",
                        `Bool (children = 0 || s.kind = "Gsave");
                        "smt", `Bool (tok = "smt" || tok = "smt.");
                        "admit", `Bool (tok = "admit" || tok = "admit.");
                        "fragile",
                        `Bool
                          (tok = "progress" || tok = "progress."
                           || (String.length s.src > 0
                               && String.contains s.src '!'));
                      ] :: !sentences))
            body
        with Exit -> ());
       Ok
         (`Assoc [
            "lemma", `String lemma;
            "split_points", `Int !splits;
            "sentences", `List (List.rev !sentences);
            "obligations", `List (List.rev !obligations);
            "uuid", `Int (Ec_llm_session.current_uuid e.session);
          ],
          !failed))

let tool_proof_outline t args =
  match str_arg args "lemma" with
  | None -> Error "proof_outline: missing required argument 'lemma'"
  | Some lemma ->
    (match find_session t args with
     | Error e -> Error e
     | Ok (label, e) ->
       if stale_flag e then
         Error "proof_outline: file changed on disk — resync_file first"
       else
         (match outline_engine e lemma with
          | Error m -> Error ("proof_outline: " ^ m)
          | Ok (payload, failed) ->
            let extra =
              match failed with
              | None -> [ "ok", `Bool true ]
              | Some (s, er) ->
                [ "ok", `Bool false;
                  "error", `String er;
                  "failed_at",
                  `Assoc [ "src", `String s.src;
                           "start_line", `Int s.start_line ] ]
            in
            (match payload with
             | `Assoc kvs ->
               Ok (`Assoc (("session", `String label) :: kvs @ extra))
             | j -> Ok j)))

let tool_proof_profile t args =
  match str_arg args "lemma" with
  | None -> Error "proof_profile: missing required argument 'lemma'"
  | Some lemma ->
    (match find_session t args with
     | Error e -> Error e
     | Ok (label, e) ->
       if stale_flag e then
         Error "proof_profile: file changed on disk — resync_file first"
       else
         (match outline_engine e lemma with
          | Error m -> Error ("proof_profile: " ^ m)
          | Ok (payload, failed) ->
            let open Yojson.Safe.Util in
            let sentences =
              match member "sentences" payload with
              | `List l -> l
              | _ -> []
            in
            (* Aggregate per branch path. *)
            let tbl : (string, int ref * int ref * int ref * int ref * int ref)
                Hashtbl.t = Hashtbl.create 8 in
            List.iter
              (fun s ->
                 let path =
                   match member "path" s with `String p -> p | _ -> ""
                 in
                 let (cnt, tms, smt, adm, fra) =
                   match Hashtbl.find_opt tbl path with
                   | Some x -> x
                   | None ->
                     let x =
                       (ref 0, ref 0, ref 0, ref 0, ref 0)
                     in
                     Hashtbl.add tbl path x;
                     x
                 in
                 incr cnt;
                 (match member "time_ms" s with
                  | `Int n -> tms := !tms + n
                  | _ -> ());
                 if member "smt" s = `Bool true then incr smt;
                 if member "admit" s = `Bool true then incr adm;
                 if member "fragile" s = `Bool true then incr fra)
              sentences;
            let branches =
              Hashtbl.fold
                (fun path (cnt, tms, smt, adm, fra) acc ->
                   `Assoc [
                     "path", `String path;
                     "sentences", `Int !cnt;
                     "time_ms", `Int !tms;
                     "smt_count", `Int !smt;
                     "admit_count", `Int !adm;
                     "fragile_count", `Int !fra;
                   ] :: acc)
                tbl []
              |> List.sort (fun a b ->
                  match member "time_ms" b, member "time_ms" a with
                  | `Int x, `Int y -> compare x y
                  | _ -> 0)
            in
            let total f =
              List.fold_left
                (fun acc s ->
                   match member f s with
                   | `Bool true -> acc + 1
                   | _ -> acc)
                0 sentences
            in
            Ok (`Assoc ([
              "session", `String label;
              "lemma", `String lemma;
              "branches", `List branches;
              "total_sentences", `Int (List.length sentences);
              "total_smt", `Int (total "smt");
              "total_admits", `Int (total "admit");
              "total_fragile", `Int (total "fragile");
              "split_points", member "split_points" payload;
            ] @ (match failed with
                 | None -> [ "ok", `Bool true ]
                 | Some (_, er) ->
                   [ "ok", `Bool false; "error", `String er ])))))

(* check_script with `admit.`-holes: verifies a restructured
   SKELETON at admit speed, reporting each hole's branch path +
   goal snapshot; state restored afterward. *)
let tool_check_skeleton t args =
  match str_arg args "script" with
  | None -> Error "check_skeleton: missing required argument 'script'"
  | Some script ->
    (match find_session t args with
     | Error e -> Error e
     | Ok (label, e) ->
       (match Ec_llm_session.parse_source e.session script with
        | Error err ->
          Error
            (Printf.sprintf "check_skeleton: script parse failed: %s"
               (Error.to_string err))
        | Ok ss ->
          let start = Ec_llm_session.current_uuid e.session in
          let corr = Correlation.of_client "mcp-skeleton" in
          let st = Frame_stack.make () in
          let count = ref (fst (goals_info e.session)) in
          let holes = ref [] in
          let failed = ref None in
          let goals_fail = ref `Null in
          (try
             List.iter
               (fun (s : Ec_llm_session.parsed_sentence) ->
                  match sentence_class_of s with
                  | None -> ()
                  | Some cls ->
                    let path = Frame_stack.path st in
                    let tok = first_token s.src in
                    let is_hole = tok = "admit" || tok = "admit." in
                    (if is_hole then
                       match goals_info e.session with
                       | (_, sub :: _) ->
                         holes :=
                           `Assoc [
                             "path", `String path;
                             "hash", `String (subgoal_hash sub);
                             "goal", sub;
                           ] :: !holes
                       | _ -> ());
                    (match
                       Ec_llm_session.exec e.session ~corr
                         ~sentence_class:cls ~source:s.src
                     with
                     | Error er ->
                       failed := Some (s, Error.to_string er);
                       goals_fail := goals_json e.session;
                       raise Exit
                     | Ok _ ->
                       let (n, _) = goals_info e.session in
                       let children = n - !count + 1 in
                       if s.kind <> "Gsave" then
                         ignore (Frame_stack.apply st ~children);
                       count := n))
               ss
           with Exit -> ());
          let closes = !failed = None && goals_closed e.session in
          let restore =
            if Ec_llm_session.current_uuid e.session = start then
              `String "unmoved"
            else
              (match
                 Ec_llm_session.revert_to_uuid e.session ~target:start
               with
               | Ok () -> `String "restored"
               | Error er ->
                 `String ("RESTORE FAILED: " ^ Error.to_string er))
          in
          Ok (`Assoc ([
            "session", `String label;
            "ok", `Bool (!failed = None);
            "closes_with_holes", `Bool closes;
            "holes", `List (List.rev !holes);
            "restore", restore;
            "uuid", `Int (Ec_llm_session.current_uuid e.session);
          ] @ (match !failed with
               | None -> []
               | Some (s, er) ->
                 [ "error", `String er;
                   "goals_at_failure", !goals_fail;
                   "failed_at", `Assoc [ "src", `String s.src ] ])))))

(* Semantic bullets: claim one open subtree by TREE path; exec_in
   then gates every sentence by goal-count containment plus a
   lexical gate on focus-moving / proof-closing input. *)
let tool_claim_subgoal t args =
  match str_arg args "path" with
  | None -> Error "claim_subgoal: missing required argument 'path'"
  | Some path ->
    (match find_session t args with
     | Error e -> Error e
     | Ok (label, e) ->
       (match e.subclaim with
        | Some sc when (not sc.sc_closed) && not (bool_arg args "force") ->
          Error
            (Printf.sprintf
               "claim_subgoal: session '%s' already has an open claim \
                on subtree %s (force=true to abandon it)"
               label sc.sc_path)
        | _ ->
          (match Ec_llm_session.raw_command e.session "TREE" with
           | Error err -> Error (Error.to_string err)
           | Ok (body, _) ->
             let paths = tree_paths body in
             let under =
               List.filter
                 (fun p ->
                    p = path
                    || (String.length p > String.length path
                        && String.sub p 0 (String.length path + 1)
                           = path ^ "."))
                 paths
             in
             (match under with
              | [] ->
                Error
                  (Printf.sprintf
                     "claim_subgoal: no open subtree at path %s \
                      (open leaves: %s)"
                     path (String.concat ", " paths))
              | first_leaf :: _ ->
                (match
                   Ec_llm_session.raw_command e.session
                     ("FOCUS " ^ first_leaf)
                 with
                 | Error err -> Error (Error.to_string err)
                 | Ok _ ->
                   let (_, subs) = goals_info e.session in
                   (match subs with
                    | [] -> Error "claim_subgoal: no open goals"
                    | entry_goal :: _ ->
                      let sc = {
                        sc_path = path;
                        sc_entry_hash = subgoal_hash entry_goal;
                        sc_remaining = List.length under;
                        sc_transcript = [];
                        sc_closed = false;
                      } in
                      e.subclaim <- Some sc;
                      e.synced_upto <- -1;
                      Ok (`Assoc [
                        "session", `String label;
                        "subgoal", `String path;
                        "remaining_in_subtree",
                        `Int sc.sc_remaining;
                        "entry_hash", `String sc.sc_entry_hash;
                        "entry_goal", entry_goal;
                        "uuid",
                        `Int (Ec_llm_session.current_uuid e.session);
                      ])))))))

let tool_exec_in t args =
  match str_arg args "text" with
  | None -> Error "exec_in: missing required argument 'text'"
  | Some text ->
    (match find_session t args with
     | Error e -> Error e
     | Ok (label, e) ->
       (match e.subclaim with
        | None ->
          Error "exec_in: no claimed subtree — call claim_subgoal first"
        | Some sc when sc.sc_closed ->
          Error
            (Printf.sprintf
               "exec_in: subtree %s is already closed" sc.sc_path)
        | Some sc ->
          (match Ec_llm_session.parse_source e.session text with
           | Error err ->
             Error
               (Printf.sprintf "exec_in: parse failed: %s"
                  (Error.to_string err))
           | Ok ss ->
             (* Lexical gate: no proof closers (skeleton owner's
                business) and no focus-moving tactics. *)
             let bad =
               List.find_opt
                 (fun (s : Ec_llm_session.parsed_sentence) ->
                    s.kind = "Gsave" || first_token s.src = "cycle")
                 ss
             in
             (match bad with
              | Some s ->
                Error
                  (Printf.sprintf
                     "exec_in: '%s' is not allowed inside a claimed \
                      subtree (closers and cycle escape the claim)"
                     (first_token s.src))
              | None ->
                let snapshot =
                  Ec_llm_session.current_uuid e.session
                in
                let corr = Correlation.of_client "mcp-execin" in
                let count = ref (fst (goals_info e.session)) in
                let remaining = ref sc.sc_remaining in
                let executed = ref [] in
                let err_ref = ref None in
                (try
                   List.iter
                     (fun (s : Ec_llm_session.parsed_sentence) ->
                        match sentence_class_of s with
                        | None -> ()
                        | Some cls ->
                          if !remaining = 0 then begin
                            err_ref :=
                              Some
                                "subtree closed before the end of \
                                 the sequence";
                            raise Exit
                          end;
                          (match
                             Ec_llm_session.exec e.session ~corr
                               ~sentence_class:cls ~source:s.src
                           with
                           | Error er ->
                             err_ref := Some (Error.to_string er);
                             raise Exit
                           | Ok _ ->
                             let (n, _) = goals_info e.session in
                             remaining := !remaining + (n - !count);
                             count := n;
                             executed := s.src :: !executed;
                             if !remaining < 0 then begin
                               err_ref :=
                                 Some
                                   "containment violation: sequence \
                                    closed goals outside the claimed \
                                    subtree";
                               raise Exit
                             end))
                     ss
                 with Exit -> ());
                (match !err_ref with
                 | Some er ->
                   (* Transactional: revert the whole sequence. *)
                   (match
                      Ec_llm_session.revert_to_uuid e.session
                        ~target:snapshot
                    with
                    | Ok () ->
                      Error
                        (Printf.sprintf
                           "exec_in: %s — sequence reverted" er)
                    | Error rer ->
                      Error
                        (Printf.sprintf
                           "exec_in: %s — AND revert failed (%s); \
                            resync_file to recover"
                           er (Error.to_string rer)))
                 | None ->
                   e.synced_upto <- -1;
                   sc.sc_remaining <- !remaining;
                   sc.sc_transcript <-
                     List.rev_append !executed sc.sc_transcript;
                   if !remaining = 0 then sc.sc_closed <- true;
                   Ok (`Assoc ([
                     "session", `String label;
                     "subgoal", `String sc.sc_path;
                     "ok", `Bool true;
                     "remaining_in_subtree", `Int !remaining;
                     "subtree_closed", `Bool sc.sc_closed;
                     "uuid",
                     `Int (Ec_llm_session.current_uuid e.session);
                     "goals", goals_json e.session;
                   ] @ (if sc.sc_closed then
                          [ "transcript",
                            `List
                              (List.rev_map
                                 (fun s -> `String s)
                                 sc.sc_transcript) ]
                        else []))))))))

(* Candidate standalone-lemma extraction from the FOCUSED goal:
   hypotheses become binders/premises, the conclusion the claim.
   v1: prop conclusions only; the output is a CANDIDATE for the
   agent to refine, not verified text. *)
let tool_extract_lemma t args =
  let name =
    match str_arg args "name" with Some n -> n | None -> "aux_extracted"
  in
  match find_session t args with
  | Error e -> Error e
  | Ok (label, e) ->
    let (_, subs) = goals_info e.session in
    (match subs with
     | [] -> Error "extract_lemma: no open goal"
     | sub :: _ ->
       let open Yojson.Safe.Util in
       let concl =
         match member "kind" (member "conclusion" sub) with
         | `String "pp" ->
           (match member "text" (member "conclusion" sub) with
            | `String s -> Ok s
            | _ -> Error "conclusion text missing")
         | _ ->
           Error
             "extract_lemma v1 supports prop conclusions only (PHL \
              judgment goals need program context)"
       in
       (match concl with
        | Error m -> Error ("extract_lemma: " ^ m)
        | Ok concl ->
          let hyps =
            match member "hypotheses" sub with `List l -> l | _ -> []
          in
          let binders = ref [] in
          let premises = ref [] in
          let skipped = ref [] in
          List.iter
            (fun h ->
               let hname =
                 match member "name" h with `String s -> s | _ -> "_"
               in
               let pp =
                 match member "pp" h with `String s -> s | _ -> ""
               in
               match member "kind" h with
               | `String "var" ->
                 binders :=
                   Printf.sprintf "(%s : %s)" hname pp :: !binders
               | `String "hyp" -> premises := pp :: !premises
               | `String k -> skipped := (hname ^ ":" ^ k) :: !skipped
               | _ -> ())
            hyps;
          let binder_str =
            match List.rev !binders with
            | [] -> ""
            | bs -> " " ^ String.concat " " bs
          in
          let stmt =
            String.concat " => " (List.rev !premises @ [ concl ])
          in
          let candidate =
            Printf.sprintf "lemma %s%s :\n  %s.\nproof.\nqed."
              name binder_str stmt
          in
          Ok (`Assoc [
            "session", `String label;
            "candidate", `String candidate;
            "call_site_hint",
            `String
              (Printf.sprintf
                 "apply %s.  (* premises become subgoals or take \
                  hypothesis names as arguments *)"
                 name);
            "skipped_hypotheses",
            `List (List.rev_map (fun s -> `String s) !skipped);
            "verified", `Bool false;
          ])))

let tool_resync_file t args =
  match find_session t args with
  | Error e -> Error e
  | Ok (label, e) ->
    let nosmt =
      match Yojson.Safe.Util.member "nosmt" args with
      | `Bool b -> b
      | _ -> true
    in
    resync_impl ~label e ~nosmt ~upto_line:(int_arg args "upto_line")
      ~at_lemma:(str_arg args "at_lemma")

(* Verified in-place proof replacement: splice [script] over the
   claimed lemma's proof-body lines, resync (weak prefix +
   full-checked tail), and RESTORE the original file if
   verification fails. The first tool with write authority — gated
   on freshness (must resync first if the file changed
   out-of-band). *)
let tool_replace_proof t args =
  match str_arg args "lemma", str_arg args "script" with
  | None, _ -> Error "replace_proof: missing required argument 'lemma'"
  | _, None -> Error "replace_proof: missing required argument 'script'"
  | Some lemma, Some script ->
    (match find_session t args with
     | Error e -> Error e
     | Ok (label, e) ->
       if stale_flag e then
         Error
           "replace_proof: file changed on disk since this session \
            last synced — run resync_file first"
       else
         let claim =
           match e.mode with
           | Proof cs ->
             (match List.find_opt (fun c -> c.lemma = lemma) cs with
              | Some c -> Ok c
              | None ->
                Error
                  (Printf.sprintf
                     "replace_proof: lemma '%s' is not claimed by \
                      session '%s' (claims: %s)"
                     lemma label
                     (String.concat ", " (claim_names e.mode))))
           | Statement ->
             (match resolve_claims e.parsed [ lemma ] with
              | Ok [ c ] -> Ok c
              | Ok _ -> Error "replace_proof: internal claim error"
              | Error m -> Error ("replace_proof: " ^ m))
         in
         (match claim with
          | Error m -> Error m
          | Ok c ->
            if c.end_line <= c.decl_end_line then
              Error
                (Printf.sprintf
                   "replace_proof: lemma '%s' has no separate proof \
                    body (declaration ends at line %d, region ends \
                    at %d)"
                   lemma c.decl_end_line c.end_line)
            else begin
              let orig = e.text in
              let lines = String.split_on_char '\n' orig in
              let pre =
                List.filteri (fun i _ -> i < c.decl_end_line) lines
              in
              let post =
                List.filteri (fun i _ -> i >= c.end_line) lines
              in
              let script_lines =
                String.split_on_char '\n' (String.trim script)
              in
              let candidate =
                String.concat "\n" (pre @ script_lines @ post)
              in
              let nosmt =
                match Yojson.Safe.Util.member "nosmt" args with
                | `Bool b -> b
                | _ -> true
              in
              (match write_file e.file candidate with
               | exception Sys_error m ->
                 Error (Printf.sprintf "replace_proof: %s" m)
               | () ->
                 (match resync_impl ~label e ~nosmt ~upto_line:None ~at_lemma:None with
                  | Error m ->
                    (try write_file e.file orig with _ -> ());
                    ignore
                      (resync_impl ~label e ~nosmt ~upto_line:None ~at_lemma:None);
                    Error
                      (Printf.sprintf
                         "replace_proof: verification could not run \
                          (%s); file restored"
                         m)
                  | Ok payload ->
                    let ok =
                      match Yojson.Safe.Util.member "ok" payload with
                      | `Bool b -> b
                      | _ -> false
                    in
                    if ok then
                      Ok (`Assoc [
                        "ok", `Bool true;
                        "lemma", `String lemma;
                        "replaced_lines",
                        `Assoc [
                          "from", `Int (c.decl_end_line + 1);
                          "to", `Int c.end_line;
                        ];
                        "file_written", `Bool true;
                        "verification", payload;
                      ])
                    else begin
                      (try write_file e.file orig with _ -> ());
                      ignore
                        (resync_impl ~label e ~nosmt ~upto_line:None ~at_lemma:None);
                      Ok (`Assoc [
                        "ok", `Bool false;
                        "lemma", `String lemma;
                        "file_restored", `Bool true;
                        "verification", payload;
                      ])
                    end))
            end))

(* ---------------------------------------------------------------- *)
(* Tool registry                                                      *)
(* ---------------------------------------------------------------- *)

let schema ?(required = []) props : Yojson.Safe.t =
  `Assoc [
    "type", `String "object";
    "properties",
    `Assoc
      (List.map
         (fun (name, ty, doc) ->
            name, `Assoc [ "type", `String ty;
                           "description", `String doc ])
         props);
    "required", `List (List.map (fun s -> `String s) required);
  ]

let session_prop =
  ("session", "string",
   "Session label (default \"main\"). Use distinct labels to run \
    parallel sessions, e.g. one per lemma/agent.")

let tools :
  (string * string * Yojson.Safe.t
   * (t -> Yojson.Safe.t -> (Yojson.Safe.t, string) result)) list = [
  "open_file",
  "Open an EasyCrypt file in a (new) proof session: spawns an EC \
   subprocess with its working directory at the file's directory \
   (easycrypt.project is honored) and loads the file, optionally \
   only up to a line. Use nosmt=true to weak-check the prefix fast \
   (safe when the prefix is already verified). Sessions declare an \
   EDIT MODE: mode=statement (the default) may change declarations \
   and therefore needs EXCLUSIVE access to the file — it is refused \
   while any other session has the file open; mode=proof edits \
   proof bodies only and parallelizes freely, but must claim its \
   target lemmas via 'lemmas' — overlapping claims (or an active \
   statement session) are refused, and the reply reports each \
   claim's document region. Replaces any existing session under \
   the same label, releasing its locks.",
  schema ~required:[ "path" ] [
    ("path", "string", "Path to the .ec/.eca file.");
    ("mode", "string",
     "\"statement\" (default; exclusive — may edit declarations) \
      or \"proof\" (parallel; proof bodies of claimed lemmas \
      only).");
    ("lemmas", "array",
     "Proof mode only (required there): lemma names this session \
      will work on. Locked against other proof sessions on the \
      same file.");
    ("upto_line", "integer",
     "Stop loading after the sentence ending on this line \
      (1-based). Omit to load the whole file.");
    ("nosmt", "boolean",
     "Weak-check the loaded prefix (skip SMT). Default false.");
    session_prop;
  ],
  tool_open_file;

  "exec",
  "Execute EasyCrypt input (tactics or declarations, '.'-terminated; \
   multi-sentence allowed) in the session, advancing its state. \
   Returns the new uuid and the structured goals after execution.",
  schema ~required:[ "text" ] [
    ("text", "string", "EasyCrypt source to execute.");
    session_prop;
  ],
  tool_exec;

  "query",
  "Run a read-only directive (print / search / locate ...) without \
   moving proof state. Returns its textual output.",
  schema ~required:[ "text" ] [
    ("text", "string",
     "Directive, '.'-terminated, e.g. \"print List.map.\" or \
      \"search (_ + _).\"");
    session_prop;
  ],
  tool_query;

  "search",
  "Search for lemmas / operators / axioms matching a pattern, \
   returning structured hits (qname, kind, signature). Default mode \
   is overload-tolerant (searchall): untyped patterns like \
   \"(_ <= _)\" work without type ascriptions, unioning all \
   operator overloads. strict=true uses EC's plain typed search.",
  schema ~required:[ "pattern" ] [
    ("pattern", "string",
     "Search pattern, e.g. \"(_ <= _)\" or \"(_ + _)\"; trailing \
      '.' optional.");
    ("strict", "boolean",
     "Use strict typed search instead of searchall. Default false.");
    ("limit", "integer", "Max hits returned (default 50).");
    session_prop;
  ],
  tool_search;

  "goals",
  "Structured view of the current proof state (GOALS-JSON): subgoal \
   count, hypotheses, conclusion trees (PHL judgments carry \
   structured program statements).",
  schema [ session_prop ],
  tool_goals;

  "tree",
  "Render the open-subgoal tree with dotted-path labels (matching \
   what focus accepts) and the focused goal marked.",
  schema [ session_prop ],
  tool_tree;

  "focus",
  "Rotate focus to a subgoal: path is a dotted tree path from \
   `tree` (e.g. \"2\" or \"1.2\"), or \"next\" to rotate to the \
   next open goal. Undoable (advances uuid).",
  schema [
    ("path", "string",
     "Dotted path from `tree`, or \"next\" (default).");
    session_prop;
  ],
  tool_focus;

  "try_tactic",
  "Speculatively run a tactic: executes it, captures the resulting \
   goals, then reverts — the session state is left unchanged. Use \
   for exploring candidate steps cheaply before committing with \
   exec.",
  schema ~required:[ "tactic" ] [
    ("tactic", "string", "Tactic source, '.'-terminated.");
    session_prop;
  ],
  tool_try_tactic;

  "check_script",
  "Speculatively run a multi-sentence candidate script (e.g. a \
   whole replacement proof body) from the current state: executes \
   sentence-by-sentence until the first failure, reports per-\
   sentence verdicts + timings and whether the proof CLOSES, then \
   restores the session to where it was. The refactoring inner \
   loop: iterate candidates here without touching the file, write \
   once with replace_proof when one passes.",
  schema ~required:[ "script" ] [
    ("script", "string",
     "EasyCrypt sentences ('.'-terminated, newline-separated), \
      e.g. \"proof.\\nsplit.\\ntrivial.\\nqed.\"");
    session_prop;
  ],
  tool_check_script;

  "check_skeleton",
  "Verify a restructured proof SKELETON at admit-speed: like \
   check_script, but `admit.` sentences are treated as HOLES — the \
   reply lists each hole's branch path + goal snapshot + hash so \
   holes can be discharged individually afterward (claim_subgoal / \
   parallel sessions). State restored afterward. Iterate strategy \
   first, pay for leaves later.",
  schema ~required:[ "script" ] [
    ("script", "string",
     "Skeleton sentences with admit. holes, e.g. \
      \"split.\\nadmit.\\nadmit.\\nqed.\"");
    session_prop;
  ],
  tool_check_skeleton;

  "proof_outline",
  "Materialize an existing lemma's proof STRUCTURE by replaying its \
   body (weak-checked prefix): per-sentence branch paths, timings, \
   split points, and the obligation set (per-split goal hashes + \
   one-liners). Branch scripts and obligation hashes are the raw \
   material for similarity spotting and before/after obligation \
   diffs. REPOSITIONS the session to the lemma's end.",
  schema ~required:[ "lemma" ] [
    ("lemma", "string", "Lemma whose proof to outline.");
    session_prop;
  ],
  tool_proof_outline;

  "proof_profile",
  "Hotspot ranking over a lemma's proof, aggregated per branch: \
   sentence counts, time, smt/admit counts, fragility markers \
   (progress, !-rewrites). Same replay as proof_outline \
   (repositions the session); use it to decide WHAT is worth \
   restructuring before deciding how.",
  schema ~required:[ "lemma" ] [
    ("lemma", "string", "Lemma whose proof to profile.");
    session_prop;
  ],
  tool_proof_profile;

  "claim_subgoal",
  "Semantic bullets: claim one open subtree (dotted TREE path) as \
   this session's work unit. Focus moves to it; exec_in then \
   enforces containment. One open claim per session — true \
   intra-proof parallelism is one worker session per subgoal. \
   Returns the entry goal + hash (guards against upstream drift) \
   and the subtree's open-leaf count.",
  schema ~required:[ "path" ] [
    ("path", "string", "Dotted subtree path from `tree`, e.g. \"2\" \
                        or \"1.2\".");
    ("force", "boolean",
     "Abandon an existing open claim on this session.");
    session_prop;
  ],
  tool_claim_subgoal;

  "exec_in",
  "Execute a tactic sequence INSIDE the claimed subtree, \
   transactionally: closers (qed/save) and cycle are refused, \
   goal-count containment is checked after every sentence, and any \
   violation or failure reverts the whole sequence. Reports \
   remaining-in-subtree and subtree_closed (with the accumulated \
   transcript on close) — bullets are re-generated by commit_proof \
   at text-assembly time, not policed during authoring.",
  schema ~required:[ "text" ] [
    ("text", "string",
     "Tactic sentences ('.'-terminated) for the claimed subtree.");
    session_prop;
  ],
  tool_exec_in;

  "extract_lemma",
  "Candidate standalone-lemma extraction from the focused goal: \
   var hypotheses become binders, hyp hypotheses premises, the \
   conclusion the claim. v1 handles prop conclusions only and \
   closes over ALL hypotheses — the output is an UNVERIFIED \
   candidate for the agent to refine, plus a call-site hint.",
  schema [
    ("name", "string",
     "Name for the extracted lemma (default aux_extracted).");
    session_prop;
  ],
  tool_extract_lemma;

  "revert",
  "Revert the session to an earlier uuid (as reported by exec / \
   goals).",
  schema ~required:[ "uuid" ] [
    ("uuid", "integer", "Target uuid to revert to.");
    session_prop;
  ],
  tool_revert;

  "commit_proof",
  "Emit the session's successfully-executed proof phrases as a \
   bullet-structured proof body (safe under +strict_bullets) — the \
   bridge from session-first exploration back into document text.",
  schema [ session_prop ],
  tool_commit_proof;

  "resync_file",
  "Re-sync the session with its (edited) file incrementally: diffs \
   the new text against the loaded snapshot, weak-checks the \
   unchanged prefix (nosmt, default true), then FULL-checks the \
   changed tail sentence-by-sentence. Reports the edit \
   classification — proof-body-only edits provably cannot affect \
   downstream lemmas; statement-changing edits are warned in proof \
   mode. Run this after ANY on-disk edit (replies carry stale=true \
   until you do). Note: session state becomes exactly the file's \
   state; interactive work not in the file is dropped.",
  schema [
    ("nosmt", "boolean",
     "Weak-check the unchanged prefix (default TRUE — the changed \
      tail is always fully checked).");
    ("upto_line", "integer",
     "Re-sync only up to this line (repositioning). Default: whole \
      file.");
    ("at_lemma", "string",
     "Position just inside this lemma's proof (after its proof. \
      sentence) — sentence-granular, works on packed lines where \
      upto_line cannot.");
    session_prop;
  ],
  tool_resync_file;

  "replace_proof",
  "Verified in-place proof replacement — the refactoring commit \
   step. Splices 'script' over the claimed lemma's proof-body \
   lines, re-syncs (weak prefix + fully-checked tail), and \
   RESTORES the original file automatically if verification \
   fails. Requires freshness (resync_file first if the file \
   changed out-of-band) and, in proof mode, a claim on the lemma. \
   This is the only tool that writes files.",
  schema ~required:[ "lemma"; "script" ] [
    ("lemma", "string", "The claimed lemma whose proof to replace.");
    ("script", "string",
     "The new proof body, from \"proof.\" through \"qed.\" \
      (newline-separated sentences).");
    ("nosmt", "boolean",
     "Weak-check the unchanged prefix during verification \
      (default true).");
    session_prop;
  ],
  tool_replace_proof;

  "analyze_file",
  "Whole-file batch diagnostics (stateless; the session's state is \
   untouched): parse/type/tactic errors with positions, sentence \
   classes and enclosing-scope tags.",
  schema ~required:[ "path" ] [
    ("path", "string", "Path to the .ec/.eca file to analyze.");
    session_prop;
  ],
  tool_analyze_file;

  "list_sessions",
  "List open proof sessions (label, file, uuid).",
  schema [],
  tool_list_sessions;

  "close_session",
  "Close a proof session and release its EC subprocess.",
  schema [ session_prop ],
  tool_close_session;
]

let tools_list_json () : Yojson.Safe.t =
  `Assoc [
    "tools",
    `List
      (List.map
         (fun (name, desc, sch, _) ->
            `Assoc [
              "name", `String name;
              "description", `String desc;
              "inputSchema", sch;
            ])
         tools);
  ]

(* ---------------------------------------------------------------- *)
(* JSON-RPC plumbing                                                  *)
(* ---------------------------------------------------------------- *)

let write_json ~stdout (j : Yojson.Safe.t) =
  Eio.Flow.copy_string (Yojson.Safe.to_string j ^ "\n") stdout

let respond ~stdout ~id result =
  write_json ~stdout
    (`Assoc [ "jsonrpc", `String "2.0"; "id", id; "result", result ])

let respond_error ~stdout ~id code message =
  write_json ~stdout
    (`Assoc [
       "jsonrpc", `String "2.0";
       "id", id;
       "error", `Assoc [ "code", `Int code; "message", `String message ];
     ])

let tool_result_json payload ~is_error : Yojson.Safe.t =
  let text =
    match payload with
    | `String s -> s
    | j -> Yojson.Safe.to_string j
  in
  `Assoc [
    "content",
    `List [ `Assoc [ "type", `String "text"; "text", `String text ] ];
    "isError", `Bool is_error;
  ]

let handle_tools_call t ~stdout ~id params =
  let name =
    match str_arg params "name" with Some n -> n | None -> ""
  in
  let args =
    match Yojson.Safe.Util.member "arguments" params with
    | `Assoc _ as a -> a
    | _ -> `Assoc []
  in
  match
    List.find_opt (fun (n, _, _, _) -> n = name) tools
  with
  | None ->
    respond_error ~stdout ~id (-32602)
      (Printf.sprintf "unknown tool: %s" name)
  | Some (_, _, _, handler) ->
    let result =
      try handler t args
      with exn ->
        Error
          (Printf.sprintf "internal error in tool %s: %s" name
             (Printexc.to_string exn))
    in
    (match result with
     | Ok payload ->
       respond ~stdout ~id (tool_result_json payload ~is_error:false)
     | Error msg ->
       respond ~stdout ~id
         (tool_result_json (`String msg) ~is_error:true))

let handle_initialize ~stdout ~id params =
  let proto =
    match str_arg params "protocolVersion" with
    | Some v -> v
    | None -> "2024-11-05"
  in
  respond ~stdout ~id
    (`Assoc [
       "protocolVersion", `String proto;
       "capabilities",
       `Assoc [ "tools", `Assoc [ "listChanged", `Bool false ] ];
       "serverInfo",
       `Assoc [
         "name", `String "ecd-mcp";
         "version", `String server_version;
       ];
       "instructions",
       `String
         "EasyCrypt proof sessions over MCP. Start with open_file \
          (optionally upto_line + nosmt for a fast prefix), inspect \
          with goals/tree, explore with try_tactic (state-neutral), \
          advance with exec, and extract the finished script with \
          commit_proof. Parallel work: give each agent its own \
          {\"session\": label} opened with mode=\"proof\" plus a \
          'lemmas' claim list — claims lock those lemmas against \
          other sessions. Changing declarations requires \
          mode=\"statement\" (the default), which needs the file \
          exclusively: close the proof sessions first, edit, then \
          re-dispatch. Refactoring loop: iterate candidates \
          in-session with check_script (state-restoring, per-\
          sentence timings); commit the winner with replace_proof \
          (verifies and auto-restores the file on failure); after \
          any other on-disk edit run resync_file — replies carry \
          stale=true until you do.";
     ])

let handle_message t ~stdout (msg : Yojson.Safe.t) =
  let member = Yojson.Safe.Util.member in
  let id = member "id" msg in
  let meth =
    match member "method" msg with `String m -> m | _ -> ""
  in
  let params =
    match member "params" msg with
    | `Assoc _ as p -> p
    | _ -> `Assoc []
  in
  match id, meth with
  (* Notifications (no id): nothing to answer. *)
  | `Null, _ -> ()
  | _, "initialize" -> handle_initialize ~stdout ~id params
  | _, "ping" -> respond ~stdout ~id (`Assoc [])
  | _, "tools/list" -> respond ~stdout ~id (tools_list_json ())
  | _, "tools/call" -> handle_tools_call t ~stdout ~id params
  | _, m ->
    respond_error ~stdout ~id (-32601)
      (Printf.sprintf "method not found: %s" m)

(* ---------------------------------------------------------------- *)
(* Main loop                                                          *)
(* ---------------------------------------------------------------- *)

let run ~sw ~stdin ~stdout =
  let t = { sw; sessions = Hashtbl.create 4 } in
  let buf = Eio.Buf_read.of_flow ~max_size:(1 lsl 24) stdin in
  let rec loop () =
    match Eio.Buf_read.line buf with
    | exception End_of_file -> ()
    | line ->
      let line = String.trim line in
      if line = "" then loop ()
      else begin
        (match Yojson.Safe.from_string line with
         | exception _ ->
           respond_error ~stdout ~id:`Null (-32700) "parse error"
         | msg -> handle_message t ~stdout msg);
        loop ()
      end
  in
  loop ();
  (* EOF: release every EC subprocess before returning. *)
  Hashtbl.iter
    (fun _ e -> try Ec_llm_session.close e.session with _ -> ())
    t.sessions;
  Hashtbl.reset t.sessions
