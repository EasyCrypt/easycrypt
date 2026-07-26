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
  lemma      : string;
  start_line : int;
  end_line   : int;
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

type entry = {
  session : Ec_llm_session.t;
  file    : string;   (* canonical path — the lock-pool key *)
  mode    : mode;
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

(* Extract the declared name from a proof-opening declaration's
   SOURCE text (not pp output): skip local/declare prefixes and
   nosmt / [attribute] tokens after the keyword; the name is the
   leading identifier of the next token. v1 heuristic — validation
   errors list every declaration found, so mismatches are visible. *)
let decl_name (src : string) : string option =
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
      Ok { lemma = n; start_line = a; end_line = b }
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
                 (fun l -> { lemma = l; start_line = 0; end_line = 0 })
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
           (* Resolve claims against the file's sentence structure
              (stateless PARSE frame on the fresh session). *)
           let resolved_mode =
             match wanted with
             | `Statement -> Ok Statement
             | `Proof ls ->
               (match read_file path with
                | exception Sys_error m ->
                  Error (Printf.sprintf "open_file: %s" m)
                | text ->
                  (match Ec_llm_session.parse_source session text with
                   | Error e ->
                     Error
                       (Printf.sprintf "open_file: parse failed: %s"
                          (Error.to_string e))
                   | Ok ss ->
                     (match
                        resolve_claims (Array.of_list ss) ls
                      with
                      | Error e -> Error ("open_file: " ^ e)
                      | Ok cs -> Ok (Proof cs))))
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
              (match Ec_llm_session.raw_command session load_cmd with
               | Error e ->
                 fail
                   (Printf.sprintf "open_file: LOAD failed: %s"
                      (Error.to_string e))
               | Ok (body, _notices) ->
                 Hashtbl.replace t.sessions label
                   { session; file = path; mode };
                 Ok (`Assoc [
                   "session", `String label;
                   "file", `String path;
                   "mode", `String (mode_label mode);
                   "claims", claims_json mode;
                   "uuid",
                   `Int (Ec_llm_session.current_uuid session);
                   "load_output", `String body;
                   "goals", goals_json session;
                 ]))))
    end

let tool_exec t args =
  match str_arg args "text" with
  | None -> Error "exec: missing required argument 'text'"
  | Some text ->
    (match find_session t args with
     | Error e -> Error e
     | Ok (label, e) ->
       let corr = Correlation.of_client "mcp-exec" in
       (match
          Ec_llm_session.exec e.session ~corr
            ~sentence_class:`Executable ~source:text
        with
        | Error err -> Error (Error.to_string err)
        | Ok ok ->
          Ok (`Assoc [
            "session", `String label;
            "uuid", `Int ok.replied_uuid;
            "restarted", `Bool ok.restarted;
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
       Ok (`Assoc [ "session", `String label; "proof", `String body ]))

let tool_analyze_file t args =
  match str_arg args "path" with
  | None -> Error "analyze_file: missing required argument 'path'"
  | Some path ->
    let path = absolute path in
    (match find_session t args with
     | Error e -> Error e
     | Ok (label, e) ->
       let cmd = Printf.sprintf "ANALYZE-JSON \"%s\"" path in
       (match Ec_llm_session.raw_command e.session cmd with
        | Error err -> Error (Error.to_string err)
        | Ok (body, _) ->
          Ok (`Assoc [
            "session", `String label;
            "file", `String path;
            "analysis", json_or_string body;
          ])))

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
          re-dispatch.";
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
