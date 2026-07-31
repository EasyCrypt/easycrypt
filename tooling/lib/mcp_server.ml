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
  (* Session-lexical bindings: $name in EC-bound tool inputs expands
     to the bound text before parsing (round 4 — long invariants are
     sent once, referenced everywhere). *)
  mutable defines : (string * string) list;
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

(* One-line goal digest: the pp's FIRST LINE (EC's own break points
   beat a mid-token cut), then a token-boundary trim if that line is
   still oversized (round 4 nit). *)
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
  let (line, more) =
    match String.index_opt s '\n' with
    | Some i -> (String.sub s 0 i, true)
    | None -> (s, false)
  in
  if String.length line <= 80 then
    (if more then line ^ " …" else line)
  else
    let cut =
      match String.rindex_from_opt line 79 ' ' with
      | Some i when i > 0 -> i
      | _ ->
        (* no token boundary in reach — cut at a UTF-8 boundary *)
        let n = ref 79 in
        while !n > 0 && Char.code line.[!n] land 0xC0 = 0x80 do
          decr n
        done;
        !n
    in
    String.sub line 0 cut ^ " …"

(* Replies echo at most a ONE-LINE PREVIEW of input the caller
   already has (round 4): full sources survive only where they ARE
   the payload — the failing sentence, transcripts, file-sourced
   outline rows. *)
let src_preview (s : string) =
  let s = String.trim s in
  let line =
    match String.index_opt s '\n' with
    | Some i -> String.sub s 0 i ^ " …"
    | None -> s
  in
  if String.length line <= 64 then line
  else begin
    let n = ref 60 in
    while !n > 0 && Char.code line.[!n] land 0xC0 = 0x80 do decr n done;
    String.sub line 0 !n ^ "…"
  end

(* ---------------------------------------------------------------- *)
(* Session-lexical bindings (round 4): define {name, text} binds a
   name on the session; `$name` in any EC-bound tool input expands
   BEFORE parsing. Purely lexical and single-pass — no recursion (a
   define's text may not itself reference defines), unknown names
   are hard errors, `<$` (EC's sampling operator) never starts a
   reference, and a session with no defines gets no scan at all.
   Honesty rule: whenever expansion changed an input, the reply
   echoes the full expanded source as `src_expanded`; files and
   transcripts only ever carry expanded EC text.                    *)

let is_ident_start c =
  (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c = '_'

let is_ident_char c =
  is_ident_start c || (c >= '0' && c <= '9') || c = '\''

(* (start position, name) of each $name reference, left to right.
   Expansion applies to CODE only: comment spans (nesting-aware) and
   string literals (backslash escapes) are skipped entirely — no
   expansion and no unknown-$ errors inside them. The file is what
   humans read (field report B9). *)
let scan_define_refs (s : string) =
  let n = String.length s in
  let out = ref [] in
  let i = ref 0 in
  while !i < n do
    match s.[!i] with
    | '(' when !i + 1 < n && s.[!i + 1] = '*' ->
      let j = ref (!i + 2) in
      let depth = ref 1 in
      while !depth > 0 && !j < n do
        if !j + 1 < n && s.[!j] = '(' && s.[!j + 1] = '*' then begin
          incr depth; j := !j + 2
        end
        else if !j + 1 < n && s.[!j] = '*' && s.[!j + 1] = ')' then begin
          decr depth; j := !j + 2
        end
        else incr j
      done;
      i := !j
    | '"' ->
      let j = ref (!i + 1) in
      while !j < n && s.[!j] <> '"' do
        if s.[!j] = '\\' && !j + 1 < n then j := !j + 2 else incr j
      done;
      i := (if !j < n then !j + 1 else n)
    | '$' when (!i = 0 || s.[!i - 1] <> '<')
               && !i + 1 < n
               && is_ident_start s.[!i + 1] ->
      let j = ref (!i + 1) in
      while !j < n && is_ident_char s.[!j] do incr j done;
      out := (!i, String.sub s (!i + 1) (!j - !i - 1)) :: !out;
      i := !j
    | _ -> incr i
  done;
  List.rev !out

let expand_defines (e : entry) (s : string) :
  (string * bool, string) result =
  if e.defines = [] then Ok (s, false)
  else
    match scan_define_refs s with
    | [] -> Ok (s, false)
    | refs ->
      let unknown =
        List.filter
          (fun (_, nm) -> not (List.mem_assoc nm e.defines))
          refs
      in
      if unknown <> [] then
        Error
          (Printf.sprintf
             "undefined $-reference%s: %s (defined: %s)"
             (if List.length unknown > 1 then "s" else "")
             (String.concat ", "
                (List.map (fun (_, nm) -> "$" ^ nm) unknown))
             (String.concat ", " (List.map fst e.defines)))
      else begin
        let buf = Buffer.create (String.length s + 64) in
        let pos = ref 0 in
        List.iter
          (fun (start, nm) ->
             Buffer.add_substring buf s !pos (start - !pos);
             Buffer.add_string buf (List.assoc nm e.defines);
             pos := start + 1 + String.length nm)
          refs;
        Buffer.add_substring buf s !pos (String.length s - !pos);
        Ok (Buffer.contents buf, true)
      end

let src_expanded_field expanded text =
  if expanded then [ "src_expanded", `String text ] else []

(* ---------------------------------------------------------------- *)
(* Bounded goal payloads (field report F5): ONE transform, ONE
   parameter, applied wherever goals are emitted.
     full   — verbatim GOALS-JSON.
     shape  — program-statement bodies (the size-dominant part of
              PHL goals) elided to instruction counts; everything
              else intact.
     counts — subgoal count + one-line conclusions only.
   Reply discipline: every reply carries EXACTLY ONE terminal-state
   field — goals / goals_at_end on success, goals_at_failure on
   failure — never both. *)

let rec elide_stmts (j : Yojson.Safe.t) : Yojson.Safe.t =
  match j with
  | `Assoc kvs ->
    (match List.assoc_opt "kind" kvs with
     | Some (`String "stmt") ->
       let n =
         match List.assoc_opt "body" kvs with
         | Some (`List l) -> List.length l
         | _ -> 0
       in
       `Assoc [
         "kind", `String "stmt";
         "elided", `Bool true;
         "instr_count", `Int n;
       ]
     | _ -> `Assoc (List.map (fun (k, v) -> (k, elide_stmts v)) kvs))
  | `List l -> `List (List.map elide_stmts l)
  | x -> x

let goal_detail_of args ~default =
  match str_arg args "goal_detail" with
  | Some "full" -> `Full
  | Some "shape" -> `Shape
  | Some "counts" -> `Counts
  | _ -> default

(* Orthogonal to goal_detail (round 9, F6): WHICH goals, not how
   much of each. "focused" slices the payload to the focused
   subgoal; subgoal_count keeps reporting the true total. On a
   20-goal call-dispatch state this is the difference between an
   80 kB reply and one goal. *)
let goal_scope_of args =
  match str_arg args "goal_scope" with
  | Some "focused" -> `Focused
  | _ -> `All

let apply_goal_scope scope (j : Yojson.Safe.t) : Yojson.Safe.t =
  match scope, j with
  | `All, _ -> j
  | `Focused, `Assoc kvs ->
    (match List.assoc_opt "subgoals" kvs with
     | Some (`List (g :: _ :: _)) ->
       `Assoc
         (List.map
            (fun (k, v) ->
               if k = "subgoals" then (k, `List [ g ]) else (k, v))
            kvs
          @ [ "goal_scope", `String "focused" ])
     | _ -> j)
  | `Focused, _ -> j

let apply_goal_detail detail (j : Yojson.Safe.t) : Yojson.Safe.t =
  match detail with
  | `Full -> j
  | `Shape -> elide_stmts j
  | `Counts ->
    let open Yojson.Safe.Util in
    (match member "active" j with
     | `Bool true ->
       let subs =
         match member "subgoals" j with `List l -> l | _ -> []
       in
       `Assoc [
         "active", `Bool true;
         "subgoal_count",
         (match member "subgoal_count" j with
          | `Int n -> `Int n
          | _ -> `Int (List.length subs));
         "conclusions",
         `List (List.map (fun s -> `String (one_line_concl s)) subs);
       ]
     | _ -> j)

(* Round 10 (F13): opt-in hard cap on pretty-printed formula text —
   the third payload complaint was conclusions (whole invariants
   duplicated across `if BAD`), which scope and detail don't touch.
   Applies to "text"/"pp" string fields; the trailing … marks the
   cut (UTF-8-safe). *)
let rec truncate_pp max (j : Yojson.Safe.t) : Yojson.Safe.t =
  match j with
  | `Assoc kvs ->
    `Assoc
      (List.map
         (fun (k, v) ->
            match v with
            | `String s
              when (k = "text" || k = "pp") && String.length s > max ->
              let n = ref max in
              while !n > 0 && Char.code s.[!n] land 0xC0 = 0x80 do
                decr n
              done;
              (k, `String (String.sub s 0 !n ^ "…"))
            | _ -> (k, truncate_pp max v))
         kvs)
  | `List l -> `List (List.map (truncate_pp max) l)
  | x -> x

(* The standard goal-payload pipeline: scope (which goals), then
   detail (how much of each), then the optional max_chars cap. *)
let render_goals args ~detail session_goals =
  let j =
    apply_goal_detail detail
      (apply_goal_scope (goal_scope_of args) session_goals)
  in
  match int_arg args "max_chars" with
  | Some n when n > 0 -> truncate_pp n j
  | _ -> j

(* Entry transparency for the state-restoring loop tools (round 10,
   B12/F11): the reply says WHAT the candidate ran against — the
   focused goal's one-liner, the open-goal count, and the bullet
   stack depth — so a focus mismatch or a live mid-proof stack is
   visible in the reply instead of being inferred from a confusing
   tactic error. *)
let entry_fields session =
  let raw = goals_json session in
  let open Yojson.Safe.Util in
  match member "active" raw with
  | `Bool true ->
    let n =
      match member "subgoal_count" raw with `Int n -> n | _ -> 0
    in
    let depth = member "bullet_depth" raw in
    let g =
      match member "subgoals" raw with
      | `List (s :: _) -> `String (one_line_concl s)
      | _ -> `Null
    in
    [ "entry",
      `Assoc [
        "goal", g;
        "open_goals", `Int n;
        "bullet_depth", depth;
      ] ]
    @ (match depth with
       | `Int d when d > 0 ->
         [ "entry_note",
           `String
             (Printf.sprintf
                "checked against the session's LIVE bullet stack \
                 (depth %d) — land-equivalent only for continuation \
                 fragments; a WHOLE-BODY candidate must be checked \
                 from the lemma's proof start (resync_file \
                 {at_lemma}, bullet depth 0)"
                d) ]
       | _ -> [])
  | _ ->
    [ "entry",
      `Assoc [
        "goal", `Null; "open_goals", `Int 0; "bullet_depth", `Null;
      ] ]

(* The first EXECUTABLE keyword of a sentence: past leading
   whitespace, (nesting-aware) comments, and bullet/focus prefixes
   (`+` `-` `*`, repeated or stacked), in any interleaving, then the
   leading identifier run ("" when the sentence has none). Field
   report B6 was the THIRD defeat of a start-anchored matcher by a
   legal sentence prefix (B1/F6: comments, B6: bullets — under
   strict_bullets every frontier `admit.` is bulleted), so this is
   now the ONLY sentence tokenizer: every keyword matcher goes
   through it, and the raw first-token helper is gone. *)
let exec_keyword (src : string) =
  let n = String.length src in
  let rec skip i =
    if i >= n then i
    else
      match src.[i] with
      | ' ' | '\t' | '\n' | '\r' -> skip (i + 1)
      | '(' when i + 1 < n && src.[i + 1] = '*' ->
        let rec close j depth =
          if j + 1 >= n then n
          else if src.[j] = '(' && src.[j + 1] = '*' then
            close (j + 2) (depth + 1)
          else if src.[j] = '*' && src.[j + 1] = ')' then
            (if depth = 1 then j + 2 else close (j + 2) (depth - 1))
          else close (j + 1) depth
        in
        skip (close i 0)
      | '+' | '-' | '*' -> skip (i + 1)
      | _ -> i
  in
  let b = skip 0 in
  let rec go i = if i < n && is_ident_char src.[i] then go (i + 1) else i in
  String.sub src b (go b - b)

(* Count invocations of keyword [kw] ANYWHERE in a sentence — as a
   whole identifier token, outside comments and strings. The
   leading-keyword flag missed `by smt(...)` closers inside `have`
   sentences, under-reporting a seven-smt lemma as one (field
   report B14): an smt call is an smt call wherever it sits. *)
let count_keyword kw (src : string) =
  let n = String.length src in
  let count = ref 0 in
  let i = ref 0 in
  while !i < n do
    match src.[!i] with
    | '(' when !i + 1 < n && src.[!i + 1] = '*' ->
      let j = ref (!i + 2) in
      let depth = ref 1 in
      while !depth > 0 && !j < n do
        if !j + 1 < n && src.[!j] = '(' && src.[!j + 1] = '*' then begin
          incr depth; j := !j + 2
        end
        else if !j + 1 < n && src.[!j] = '*' && src.[!j + 1] = ')'
        then begin decr depth; j := !j + 2 end
        else incr j
      done;
      i := !j
    | '"' ->
      let j = ref (!i + 1) in
      while !j < n && src.[!j] <> '"' do
        if src.[!j] = '\\' && !j + 1 < n then j := !j + 2 else incr j
      done;
      i := (if !j < n then !j + 1 else n)
    | c when is_ident_start c ->
      let j = ref !i in
      while !j < n && is_ident_char src.[!j] do incr j done;
      if String.sub src !i (!j - !i) = kw then incr count;
      i := !j
    | _ -> incr i
  done;
  !count

(* Largest hint-list length among the sentence's smt(...) calls
   (ident tokens inside the parens). A long hint list is a measured
   fragility class (B14: the actual flake was exactly this). *)
let smt_hint_fragile_threshold = 8

let smt_hint_max (src : string) =
  let n = String.length src in
  let best = ref 0 in
  let i = ref 0 in
  while !i < n do
    match src.[!i] with
    | '(' when !i + 1 < n && src.[!i + 1] = '*' ->
      let j = ref (!i + 2) in
      let depth = ref 1 in
      while !depth > 0 && !j < n do
        if !j + 1 < n && src.[!j] = '(' && src.[!j + 1] = '*' then begin
          incr depth; j := !j + 2
        end
        else if !j + 1 < n && src.[!j] = '*' && src.[!j + 1] = ')'
        then begin decr depth; j := !j + 2 end
        else incr j
      done;
      i := !j
    | c when is_ident_start c ->
      let j = ref !i in
      while !j < n && is_ident_char src.[!j] do incr j done;
      let is_smt = String.sub src !i (!j - !i) = "smt" in
      i := !j;
      if is_smt then begin
        while !i < n && (src.[!i] = ' ' || src.[!i] = '\t') do incr i done;
        if !i < n && src.[!i] = '(' then begin
          incr i;
          let depth = ref 1 in
          let hints = ref 0 in
          while !depth > 0 && !i < n do
            match src.[!i] with
            | '(' -> incr depth; incr i
            | ')' -> decr depth; incr i
            | c when is_ident_start c ->
              let j = ref !i in
              while !j < n && is_ident_char src.[!j] do incr j done;
              incr hints;
              i := !j
            | _ -> incr i
          done;
          if !hints > !best then best := !hints
        end
      end
    | _ -> incr i
  done;
  !best

(* Sentence identity up to leading comments and surrounding
   whitespace (nesting-aware — EC comments nest): the parser attaches
   a leading comment to the FOLLOWING sentence, so a comment edit
   textually changes that sentence while its executable content is
   untouched. Comparing cores keeps comment-only edits out of the
   execution diff and the classification (field report round 4). *)
let sentence_core (src : string) =
  let n = String.length src in
  let rec skip i =
    if i >= n then i
    else
      match src.[i] with
      | ' ' | '\t' | '\n' | '\r' -> skip (i + 1)
      | '(' when i + 1 < n && src.[i + 1] = '*' ->
        let rec close j depth =
          if j + 1 >= n then n
          else if src.[j] = '(' && src.[j + 1] = '*' then
            close (j + 2) (depth + 1)
          else if src.[j] = '*' && src.[j + 1] = ')' then
            (if depth = 1 then j + 2 else close (j + 2) (depth - 1))
          else close (j + 1) depth
        in
        skip (close i 0)
      | _ -> i
  in
  let b = skip 0 in
  let rec back j =
    if j > b
       && (match src.[j - 1] with
           | ' ' | '\t' | '\n' | '\r' -> true
           | _ -> false)
    then back (j - 1)
    else j
  in
  let e = back n in
  String.sub src b (e - b)

let core_equal (a : Ec_llm_session.parsed_sentence)
    (b : Ec_llm_session.parsed_sentence) =
  a.src = b.src || sentence_core a.src = sentence_core b.src

(* Admits are HOLES wherever they execute: the goal an `admit.` is
   about to discharge is captured BEFORE the sentence runs, so every
   executing tool reports swept-under-the-rug debt uniformly in an
   "admitted" array. Bullet and comment prefixes are transparent
   (B6): `+ admit.` is exactly the shape real work-in-progress debt
   takes under strict_bullets. *)
let is_admit_sentence (s : Ec_llm_session.parsed_sentence) =
  exec_keyword s.src = "admit"

let capture_admit session detail =
  match goals_info session with
  | (_, sub :: _) ->
    Some (apply_goal_detail detail sub, subgoal_hash sub)
  | _ -> None

(* One-line-per-goal tree, attached automatically when a call GROWS
   the open-goal count (round 4): the subgoal ORDER a splitting
   tactic produces is exactly what the agent needs at that moment,
   with no extra round trip. *)
let compact_tree session : (string * Yojson.Safe.t) list =
  match Ec_llm_session.raw_command session "TREE" with
  | Error _ -> []
  | Ok (body, _) -> [ "tree", `String body ]

let tree_if_grew session ~before =
  let (after, _) = goals_info session in
  if after > before && after > 0 then compact_tree session else []

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
              (* AST-sourced name (proto 3): every declaration form,
                 banners and modifiers included, by construction. *)
              Option.map (fun n -> (n, i, s)) s.name
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
            let remedy =
              match taken with
              | (_, l) :: _ ->
                Printf.sprintf
                  " — a holder whose agent is gone releases its \
                   claims with close_session {\"session\": \"%s\"}; \
                   locks live in THIS server process only"
                  l
              | [] -> ""
            in
            Error
              (Printf.sprintf "lemma claim conflict: %s%s"
                 (String.concat ", " (List.map show taken))
                 remedy)))

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
               | Ok (ss, file_perr) ->
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
                           subclaim = None; defines = [] };
                       Ok (`Assoc [
                         "session", `String label;
                         "file", `String path;
                         "mode", `String (mode_label mode);
                         "claims", claims_json mode;
                         "uuid",
                         `Int (Ec_llm_session.current_uuid session);
                         "parse_error",
                   (match file_perr with
                    | None -> `Null
                    | Some s -> json_or_string s);
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
       (match expand_defines e text with
        | Error m -> Error ("exec: " ^ m)
        | Ok (text, expanded) ->
       (* Strict per-sentence execution (field report B5): the input
          is split by the REAL parser and each sentence executes on
          its own — successes COMMIT, the first failure stops the
          sequence, and the reply reports every sentence. The wire
          itself now rejects multi-phrase blocks (proto 3), so
          nothing can be silently dropped at any layer. *)
       (match Ec_llm_session.parse_source e.session text with
        | Error err ->
          Error
            (Printf.sprintf "exec: parse failed: %s"
               (Error.to_string err))
        | Ok (_, Some perr) ->
          Error
            (Printf.sprintf
               "exec: input has a parse error — NOTHING was \
                executed: %s"
               perr)
        | Ok (ss, None) ->
          let corr = Correlation.of_client "mcp-exec" in
          let detail = goal_detail_of args ~default:`Shape in
          let results = ref [] in
          let notices = ref [] in
          let failed = ref false in
          let restarted = ref false in
          let executed = ref 0 in
          let admitted = ref [] in
          let n_goals0 = fst (goals_info e.session) in
          let t0 = Unix.gettimeofday () in
          (try
             List.iteri
               (fun i (s : Ec_llm_session.parsed_sentence) ->
                  match sentence_class_of s with
                  | None -> ()
                  | Some cls ->
                    let s0 = Unix.gettimeofday () in
                    let adm =
                      if is_admit_sentence s then
                        capture_admit e.session detail
                      else None
                    in
                    (match
                       Ec_llm_session.exec e.session ~corr
                         ~sentence_class:cls ~source:s.src
                     with
                     | Ok ok ->
                       incr executed;
                       (match adm with
                        | Some (g, h) ->
                          admitted :=
                            `Assoc [
                              "index", `Int i;
                              "src", `String (src_preview s.src);
                              "goal", g;
                              "hash", `String h;
                            ] :: !admitted
                        | None -> ());
                       if ok.restarted then restarted := true;
                       notices := List.rev_append ok.notices !notices;
                       results :=
                         `Assoc [
                           "index", `Int i;
                           "src", `String (src_preview s.src);
                           "ok", `Bool true;
                           "uuid", `Int ok.replied_uuid;
                           "time_ms", `Int (ms_since s0);
                         ] :: !results
                     | Error er ->
                       failed := true;
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
          if !executed > 0 then e.synced_upto <- -1;
          let base = [
            "session", `String label;
            "ok", `Bool (not !failed);
            "executed", `Int !executed;
            "uuid", `Int (Ec_llm_session.current_uuid e.session);
            "restarted", `Bool !restarted;
            "time_ms", `Int (ms_since t0);
            "stale", `Bool (stale_flag e);
            "notices",
            `List (List.rev_map (fun n -> `String n) !notices);
            "sentences", `List (List.rev !results);
            "admitted", `List (List.rev !admitted);
          ] @ src_expanded_field expanded text in
          let terminal =
            if !failed then
              [ "goals_at_failure",
                render_goals args ~detail (goals_json e.session);
                "note",
                `String
                  "sentences before the failure REMAIN EXECUTED — \
                   revert {uuid} or resync_file to unwind" ]
            else
              let gp =
                render_goals args ~detail (goals_json e.session)
              in
              let closed =
                let open Yojson.Safe.Util in
                member "active" gp = `Bool false
                || member "subgoal_count" gp = `Int 0
              in
              [ "goals", gp ]
              @ tree_if_grew e.session ~before:n_goals0
              @ (if closed then
                   [ "proof_complete", `Bool true;
                     "hint",
                     `String
                       "goals closed — commit_proof {lemma, \
                        write:true} lands this proof in the file" ]
                 else [])
          in
          Ok (`Assoc (base @ terminal)))))

let tool_query t args =
  match str_arg args "text" with
  | None -> Error "query: missing required argument 'text'"
  | Some text ->
    (match find_session t args with
     | Error e -> Error e
     | Ok (label, e) ->
       (match expand_defines e text with
        | Error m -> Error ("query: " ^ m)
        | Ok (text, expanded) ->
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
          Ok (`Assoc ([
            "session", `String label;
            "output", `String output;
          ] @ src_expanded_field expanded text)))))

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
      "goals",
      render_goals args ~detail:(goal_detail_of args ~default:`Full)
        (goals_json e.session);
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

(* Exploration cost knob (round 4): a transactional `timeout N.`
   applied before a candidate runs. `timeout` is an ordinary
   undoable EC global (Gprover_info), so the tool's normal
   revert-to-start also restores the previous prover timeout —
   nothing leaks. Persistent variant: exec {text: "timeout N."}. *)
let apply_smt_timeout (e : entry) args ~corr =
  match int_arg args "smt_timeout" with
  | None -> Ok None
  | Some n when n < 1 ->
    Error "smt_timeout must be a positive number of seconds"
  | Some n ->
    (match
       Ec_llm_session.exec e.session ~document:true ~corr
         ~sentence_class:`Executable
         ~source:(Printf.sprintf "timeout %d." n)
     with
     | Ok _ -> Ok (Some n)
     | Error er ->
       Error
         (Printf.sprintf "setting `timeout %d.` failed: %s" n
            (Error.to_string er)))

let smt_timeout_field = function
  | Some n -> [ "smt_timeout", `Int n ]
  | None -> []

let tool_try_tactic t args =
  match str_arg args "tactic" with
  | None -> Error "try_tactic: missing required argument 'tactic'"
  | Some tactic ->
    (match find_session t args with
     | Error e -> Error e
     | Ok (label, e) ->
       (match expand_defines e tactic with
        | Error m -> Error ("try_tactic: " ^ m)
        | Ok (tactic, expanded) ->
       (* Single-sentence by contract (round 11, F15): refuse
          sequences in TOOL vocabulary before anything runs — the
          wire's block error is protocol-speak a caller can't act
          on. *)
       (match Ec_llm_session.parse_source e.session tactic with
        | Error err ->
          Error
            (Printf.sprintf "try_tactic: parse failed: %s"
               (Error.to_string err))
        | Ok (_, Some perr) ->
          Error
            (Printf.sprintf
               "try_tactic: parse error — nothing ran: %s" perr)
        | Ok (ss, None)
          when List.length
                 (List.filter
                    (fun s -> sentence_class_of s <> None) ss)
               > 1 ->
          Error
            "try_tactic takes ONE sentence — use try_script (the \
             state-neutral sequence probe) for \"run these and \
             show me the goal\", or check_script for a document-\
             rules candidate"
        | Ok _ ->
       let pre = Ec_llm_session.current_uuid e.session in
       let corr = Correlation.of_client "mcp-try" in
       let n_goals0 = fst (goals_info e.session) in
       (match apply_smt_timeout e args ~corr with
        | Error m -> Error ("try_tactic: " ^ m)
        | Ok applied ->
       let t0 = Unix.gettimeofday () in
       (match
          Ec_llm_session.exec e.session ~corr
            ~sentence_class:`Executable ~source:tactic
        with
        | Error err ->
          (* A failed tactic leaves uuid unmoved — but the timeout
             sentence (when given) advanced it: restore. *)
          (if applied <> None then
             ignore
               (Ec_llm_session.revert_to_uuid e.session ~target:pre));
          Ok (`Assoc ([
            "session", `String label;
            "outcome", `String "err";
            "error", `String (Error.to_string err);
          ] @ smt_timeout_field applied
            @ src_expanded_field expanded tactic))
        | Ok _ ->
          let goals_after =
            render_goals args
              ~detail:(goal_detail_of args ~default:`Shape)
              (goals_json e.session)
          in
          (* Captured BEFORE the revert: the post-candidate tree is
             gone once the state is restored. *)
          let tree_extra = tree_if_grew e.session ~before:n_goals0 in
          (match
             Ec_llm_session.revert_to_uuid e.session ~target:pre
           with
           | Ok () ->
             Ok (`Assoc ([
               "session", `String label;
               "outcome", `String "ok";
               "time_ms", `Int (ms_since t0);
               "goals_after", goals_after;
             ] @ tree_extra @ smt_timeout_field applied
               @ src_expanded_field expanded tactic @ [
               "reverted_to", `Int pre;
             ]))
           | Error err ->
             (* State is now past the candidate — surface loudly. *)
             Error
               (Printf.sprintf
                  "try_tactic: candidate applied but revert failed \
                   (%s); session '%s' state has ADVANCED"
                  (Error.to_string err) label)))))))

(* Multi-sentence STATE-NEUTRAL probe (round 11, F15): exec+revert
   as one atomic call, asked for independently by two workers. Runs
   a short AUTHORED sequence from the current state (REPL rules —
   probes are authored text, not document candidates), reports
   per-sentence verdicts and the resulting goals, then ALWAYS
   restores. This is the safe way to ask "what do these sentences
   do here": a committed exec probe poisons every later
   check_script (F10), and check_script is the document-rules
   candidate checker, not a probe. *)
let tool_try_script t args =
  match str_arg args "script" with
  | None -> Error "try_script: missing required argument 'script'"
  | Some script ->
    (match find_session t args with
     | Error e -> Error e
     | Ok (label, e) ->
       (match expand_defines e script with
        | Error m -> Error ("try_script: " ^ m)
        | Ok (script, expanded) ->
       (match Ec_llm_session.parse_source e.session script with
        | Error err ->
          Error
            (Printf.sprintf "try_script: parse failed: %s"
               (Error.to_string err))
        | Ok (_, Some perr) ->
          Error
            (Printf.sprintf
               "try_script: parse error — nothing ran: %s" perr)
        | Ok (ss, None) ->
          let start = Ec_llm_session.current_uuid e.session in
          let corr = Correlation.of_client "mcp-tryscript" in
          let detail = goal_detail_of args ~default:`Shape in
          let entry = entry_fields e.session in
          (match apply_smt_timeout e args ~corr with
           | Error m -> Error ("try_script: " ^ m)
           | Ok applied ->
          let results = ref [] in
          let admitted = ref [] in
          let failed = ref false in
          let goals_fail = ref `Null in
          let restarted = ref false in
          let n_goals0 = fst (goals_info e.session) in
          let t0 = Unix.gettimeofday () in
          (try
             List.iteri
               (fun i (s : Ec_llm_session.parsed_sentence) ->
                  match sentence_class_of s with
                  | None -> ()
                  | Some cls ->
                    let s0 = Unix.gettimeofday () in
                    let adm =
                      if is_admit_sentence s then
                        capture_admit e.session detail
                      else None
                    in
                    (match
                       Ec_llm_session.exec e.session ~corr
                         ~sentence_class:cls ~source:s.src
                     with
                     | Ok ok ->
                       if ok.restarted then begin
                         restarted := true;
                         raise Exit
                       end;
                       (match adm with
                        | Some (g, h) ->
                          admitted :=
                            `Assoc [
                              "index", `Int i;
                              "src", `String (src_preview s.src);
                              "goal", g;
                              "hash", `String h;
                            ] :: !admitted
                        | None -> ());
                       results :=
                         `Assoc [
                           "index", `Int i;
                           "src", `String (src_preview s.src);
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
          let goals_after = goals_json e.session in
          let tree_extra =
            if !failed || !restarted then []
            else tree_if_grew e.session ~before:n_goals0
          in
          let restore =
            if !restarted then
              `String
                "session restarted mid-script — state NOT \
                 restored; run resync_file to recover"
            else if Ec_llm_session.current_uuid e.session = start
            then `String "unmoved"
            else
              match
                Ec_llm_session.revert_to_uuid e.session ~target:start
              with
              | Ok () -> `String "restored"
              | Error er ->
                `String ("RESTORE FAILED: " ^ Error.to_string er)
          in
          Ok (`Assoc ([
            "session", `String label;
            "checked", `Int (List.length !results);
            "ok", `Bool ((not !failed) && not !restarted);
          ] @ entry @ [
            "results", `List (List.rev !results);
            "admitted", `List (List.rev !admitted);
            "restore", restore;
            "uuid", `Int (Ec_llm_session.current_uuid e.session);
            "total_time_ms", `Int (ms_since t0);
            "stale", `Bool (stale_flag e);
          ] @ smt_timeout_field applied
            @ src_expanded_field expanded script
            @ (if !failed then
                 [ "goals_at_failure",
                   render_goals args ~detail !goals_fail ]
               else
                 [ "goals_after",
                   render_goals args ~detail goals_after ]
                 @ tree_extra)))))))

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

(* Round 10 (F9): a 2,430-line restatement produced 201 diagnostics
   that were SIX root causes — the raw 300 kB reply buried them. The
   view ladder keeps the full dump available while making the
   default question ("what actually broke, where") one readable
   reply: diagnostics drops the sentence inventory; triage keeps the
   FIRST diagnostic per enclosing declaration and counts the
   cascades it suppressed. *)
let apply_analysis_view view (a : Yojson.Safe.t) :
  (string * Yojson.Safe.t) list =
  let open Yojson.Safe.Util in
  match view with
  | `Full -> [ "analysis", a ]
  | (`Diagnostics | `Triage) as v ->
    let diags = match member "diagnostics" a with
      | `List l -> l | _ -> [] in
    let sents = match member "sentences" a with
      | `List l -> l | _ -> [] in
    let counts =
      [ "sentence_count", `Int (List.length sents);
        "diagnostic_count", `Int (List.length diags) ]
    in
    (match v with
     | `Diagnostics -> counts @ [ "diagnostics", `List diags ]
     | `Triage ->
       let sent_arr = Array.of_list sents in
       (* Nearest named declaration at or before the diagnostic's
          sentence — module/type/op/lemma names all come from the
          AST (proto 3 + round 10). *)
       let decl_of idx =
         let rec go i =
           if i < 0 || i >= Array.length sent_arr then None
           else
             match member "name" sent_arr.(i) with
             | `String n -> Some n
             | _ -> go (i - 1)
         in
         go idx
       in
       let seen : (string, int ref) Hashtbl.t = Hashtbl.create 8 in
       let rows = ref [] in
       List.iter
         (fun d ->
            let idx =
              match member "sentence_index" d with
              | `Int i -> i
              | _ -> -1
            in
            let key =
              match decl_of idx with
              | Some n -> n
              | None -> "(preamble)"
            in
            match Hashtbl.find_opt seen key with
            | Some extra -> incr extra
            | None ->
              let extra = ref 0 in
              Hashtbl.add seen key extra;
              rows := (key, d, extra) :: !rows)
         diags;
       counts
       @ [ "root_causes", `Int (List.length !rows);
           "triage",
           `List
             (List.rev_map
                (fun (k, d, extra) ->
                   `Assoc [
                     "declaration", `String k;
                     "first_diagnostic", d;
                     "cascading_suppressed", `Int !extra;
                   ])
                !rows) ])

let tool_analyze_file t args =
  match str_arg args "path" with
  | None -> Error "analyze_file: missing required argument 'path'"
  | Some path ->
    let path = absolute path in
    let view =
      match str_arg args "view" with
      | Some "diagnostics" -> `Diagnostics
      | Some "triage" -> `Triage
      | _ -> `Full
    in
    let run session =
      let cmd = Printf.sprintf "ANALYZE-JSON \"%s\"" path in
      match Ec_llm_session.raw_command session cmd with
      | Error err -> Error (Error.to_string err)
      | Ok (body, _) ->
        Ok
          (("file", `String path)
           :: apply_analysis_view view (json_or_string body))
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
           "defines",
           `List (List.map (fun (nm, _) -> `String nm) e.defines);
           "alive", `Bool (Ec_llm_session.is_alive e.session);
           "uuid", `Int (Ec_llm_session.current_uuid e.session);
         ] :: acc)
      t.sessions []
  in
  Ok (`Assoc ([ "sessions", `List rows ]
              @ (if rows = [] then
                   [ "note",
                     `String
                       "no sessions in THIS server process — locks \
                        live per process, so if a refusal names a \
                        session that is not listed here, that call \
                        was answered by a DIFFERENT registered \
                        server instance (check the registration \
                        scope)" ]
                 else [])))

let tool_close_session t args =
  let label = label_of_args args in
  match Hashtbl.find_opt t.sessions label with
  | None -> Error (Printf.sprintf "close_session: no session '%s'" label)
  | Some e ->
    (try Ec_llm_session.close e.session with _ -> ());
    Hashtbl.remove t.sessions label;
    Ok (`Assoc [ "closed", `String label ])

(* Session-lexical bindings: set with {name, text}, delete with
   {name} alone, list with no name. The reply always carries the
   full table — the binding set is part of the session's visible
   state, never hidden context. *)
let tool_define t args =
  match find_session t args with
  | Error e -> Error e
  | Ok (label, e) ->
    let reply () =
      Ok (`Assoc [
        "session", `String label;
        "defines",
        `List
          (List.map
             (fun (nm, tx) ->
                `Assoc [ "name", `String nm; "text", `String tx ])
             e.defines);
      ])
    in
    (match str_arg args "name" with
     | None -> reply ()
     | Some name ->
       if not (String.length name > 0
               && is_ident_start name.[0]
               && String.for_all is_ident_char name)
       then
         Error
           "define: name must be an identifier \
            ([A-Za-z_][A-Za-z0-9_']*)"
       else
         (match str_arg args "text" with
          | None ->
            e.defines <- List.remove_assoc name e.defines;
            reply ()
          | Some text ->
            if String.trim text = "" then
              Error
                "define: empty text — omit 'text' to delete a \
                 binding"
            else if scan_define_refs text <> [] then
              Error
                "define: text may not reference other defines \
                 (expansion is single-pass, no recursion)"
            else begin
              e.defines <-
                (name, text) :: List.remove_assoc name e.defines;
              reply ()
            end))

(* ---------------------------------------------------------------- *)
(* Refactoring loop: check_script / resync_file / replace_proof       *)
(* ---------------------------------------------------------------- *)

(* Speculatively run a multi-sentence candidate (a whole proof body)
   from the CURRENT state: execute sentence-by-sentence until the
   first failure, report per-sentence verdicts + timing + whether
   the proof closes, then revert to the starting uuid. The session
   is left where it was. *)
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
let resync_impl ~label (e : entry) ~nosmt ~upto_line ~upto_sentence
    ~at_lemma ~goal_detail =
  match read_file e.file with
  | exception Sys_error m -> Error (Printf.sprintf "resync_file: %s" m)
  | text ->
    let unchanged = Digest.string text = e.hash in
    if unchanged && upto_line = None && at_lemma = None
       && upto_sentence = None
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
       | Ok (ss, file_perr) ->
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
                       && exec_keyword
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
             (match upto_sentence with
              | Some n -> Ok (max 0 (min n_all n))
              | None ->
             match upto_line with
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
            (* Identity is COMMENT-BLIND (sentence cores): a leading-
               comment edit does not change what executes. The
               prefix/suffix scans run over the FULL arrays —
               classification describes the EDIT; the execution
               boundary is bounded by the target separately. *)
            let core_prefix =
              let nmin = min n_old n_all in
              let rec go i =
                if i < nmin && core_equal old.(i) parsed_all.(i)
                then go (i + 1)
                else i
              in
              go 0
            in
            (* Trim the common (core-equal) suffix so unchanged
               downstream sentences don't pollute a mid-file body
               edit's classification. *)
            let ks =
              let maxs =
                min (n_old - core_prefix) (n_all - core_prefix)
              in
              let rec go i =
                if i < maxs
                   && core_equal
                        old.(n_old - 1 - i)
                        parsed_all.(n_all - 1 - i)
                then go (i + 1)
                else i
              in
              go 0
            in
            let k = min core_prefix m in
            (* Full-length core equality = formatting-only edit: the
               session's executed state is untouched by construction;
               only the snapshot (text, line numbers) needs
               replacing. *)
            let formatting_equiv =
              (not unchanged) && n_all = n_old && core_prefix = n_all
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
              window old core_prefix (n_old - ks)
              @ window parsed_all core_prefix (n_all - ks)
            in
            (* Environment-equivalence certificate (round 4): an edit
               whose every changed sentence is a proof-mode TACTIC on
               both sides cannot change the environment any
               downstream sentence sees — statements are untouched
               and save outcomes preserved (Gsave changes fail the
               certificate: qed→abort would REMOVE the lemma). Two
               ways to earn it: the contiguous diff window is all
               tactics (single-body edits, insertions/deletions
               included), or — same sentence count — every per-index
               differing pair is a tactic pair (disjoint multi-body
               edits). *)
            let per_index_body_only =
              n_old = n_all
              && (let ok = ref true and any = ref false in
                  for i = 0 to n_all - 1 do
                    if not (core_equal old.(i) parsed_all.(i))
                    then begin
                      any := true;
                      if (old.(i) : Ec_llm_session.parsed_sentence)
                           .kind <> "Gtactics"
                         || (parsed_all.(i)
                             : Ec_llm_session.parsed_sentence)
                              .kind <> "Gtactics"
                      then ok := false
                    end
                  done;
                  !ok && !any)
            in
            let body_only =
              (diff_kinds <> []
               && List.for_all (fun kd -> kd = "Gtactics") diff_kinds)
              || per_index_body_only
            in
            let classification =
              if unchanged then "reposition"
              else if formatting_equiv || diff_kinds = [] then
                "formatting-only"
              else if body_only then "proof-body-only"
              else if core_prefix >= n_old then "additive"
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
            (* Re-resolve claim regions against the new snapshot
               (line numbers move under any edit). *)
            let remap_claims () =
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
            if formatting_equiv && at_lemma = None && upto_line = None
               && upto_sentence = None
            then begin
              (* Nothing executable changed: swap the snapshot, remap
                 claim regions, and leave the session state — position
                 AND any live subgoal claim — exactly where it was. A
                 comment edit costs no reload and voids nothing. *)
              e.text <- text;
              e.hash <- Digest.string text;
              e.parsed <- parsed_all;
              let claims_warning = remap_claims () in
              Ok (`Assoc ([
                "session", `String label;
                "changed", `Bool true;
                "parse_error",
                (match file_perr with
                 | None -> `Null
                 | Some s -> json_or_string s);
                "classification", `String "formatting-only";
                "fast_forward", `Bool true;
                "common_prefix_sentences", `Int core_prefix;
                "target_sentences", `Int e.synced_upto;
                "tail_executed", `Int 0;
                "tail_skipped", `Int 0;
                "admitted", `List [];
                "prefix_time_ms", `Int 0;
                "tail_time_ms", `Int 0;
                "uuid", `Int (Ec_llm_session.current_uuid e.session);
                "stale", `Bool false;
                "claims", claims_json e.mode;
                "synced_upto", `Int e.synced_upto;
                "ok", `Bool true;
                "note",
                `String
                  "formatting-only edit (comments/whitespace): \
                   snapshot updated, session position and state \
                   preserved — nothing executable changed";
                "goals",
                apply_goal_detail goal_detail (goals_json e.session);
              ] @ claims_warning))
            end
            else begin
            let corr = Correlation.of_client "mcp-resync" in
            let admitted = ref [] in
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
                     let adm =
                       if is_admit_sentence s then
                         capture_admit e.session goal_detail
                       else None
                     in
                     (match
                        Ec_llm_session.exec e.session ~document:true
                          ~corr ~sentence_class:cls ~source:s.src
                      with
                      | Ok _ ->
                        incr cnt;
                        (match adm with
                         | Some (g, h) ->
                           admitted :=
                             `Assoc [
                               "index", `Int i;
                               "start_line", `Int s.start_line;
                               "goal", g;
                               "hash", `String h;
                             ] :: !admitted
                         | None -> ())
                      | Error er ->
                        err := Some (i, s, er);
                        raise Exit)
                 done
               with Exit -> ());
              (!cnt, !err)
            in
            (* Tail skip under the certificate (round 4): re-executing
               unchanged sentences past the edited body proves nothing
               the certificate hasn't already — stop at the enclosing
               save and leave the session there (a normal positioning
               state; forward hops fast-forward from it). Whole-file
               resyncs only: explicit targets are honored exactly. *)
            let explicit_target =
              at_lemma <> None || upto_line <> None
              || upto_sentence <> None
            in
            let m_eff, tail_skipped =
              if classification = "proof-body-only"
                 && not explicit_target
              then begin
                let rec find_save i =
                  if i >= n_all then n_all
                  else if (parsed_all.(i)
                           : Ec_llm_session.parsed_sentence).kind
                          = "Gsave"
                  then i + 1
                  else find_save (i + 1)
                in
                let stop = min m (find_save (n_all - ks)) in
                (stop, m - stop)
              end
              else (m, 0)
            in
            (* Fast when the session's executed prefix is core-valid
               against the NEW text — the file being unchanged is just
               the special case core_prefix = n_all. Editing BELOW the
               session's position no longer forces a prefix reload. *)
            let fast =
              e.synced_upto >= 0 && e.synced_upto <= m_eff
              && core_prefix >= e.synced_upto
            in
            let run () =
              if fast then begin
                let t1 = Unix.gettimeofday () in
                let (c, er) = exec_range e.synced_upto m_eff in
                Ok (true, 0, ms_since t1, c, er)
              end
              else begin
                (* Back the prefix boundary off shared end-lines so
                   the line-granular LOAD cannot overshoot past the
                   sentence-granular target (B2). *)
                let j = ref (min k m_eff) in
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
                  let (c, er) = exec_range j m_eff in
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
                  | None -> m_eff
                  | Some (i, _, _) -> i);
               let claims_warning = remap_claims () in
               let base =
                 [
                   "session", `String label;
                   "changed", `Bool (not unchanged);
                   "parse_error",
                   (match file_perr with
                    | None -> `Null
                    | Some s -> json_or_string s);
                   "classification", `String classification;
                   "fast_forward", `Bool fast_forward;
                   "common_prefix_sentences", `Int core_prefix;
                   "target_sentences", `Int m;
                   "tail_executed", `Int executed;
                   "tail_skipped", `Int tail_skipped;
                   "synced_upto", `Int e.synced_upto;
                   "admitted", `List (List.rev !admitted);
                   "prefix_time_ms", `Int prefix_ms;
                   "tail_time_ms", `Int tail_ms;
                   "uuid",
                   `Int (Ec_llm_session.current_uuid e.session);
                   "stale", `Bool false;
                   "claims", claims_json e.mode;
                 ]
                 @ (if tail_skipped > 0 then
                      [ "note",
                        `String
                          "unchanged tail after the edited body was \
                           NOT re-executed (environment-equivalence \
                           certificate: the edit is confined to \
                           proof tactics); session is positioned at \
                           the edited lemma's end — a follow-up \
                           resync_file fast-forwards to EOF if you \
                           need the whole file loaded" ]
                    else [])
                 @ warning @ claims_warning
               in
               (match err_opt with
                | None ->
               Ok
                 (`Assoc
                    (base
                     @ [
                         "ok", `Bool true;
                         "goals",
                         apply_goal_detail goal_detail
                           (goals_json e.session);
                       ]))
                | Some (i, s, er) ->
                  Ok
                    (`Assoc
                       (base
                        @ [
                            "ok", `Bool false;
                            "error", `String (Error.to_string er);
                            "goals_at_failure",
                            apply_goal_detail goal_detail
                              (goals_json e.session);
                            "failed_sentence",
                            `Assoc [
                              "index", `Int i;
                              "src", `String s.src;
                              "start_line", `Int s.start_line;
                            ];
                          ]))))
            end))
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
       (* The raw LOAD moved the session off its recorded file-prefix
          position — invalidate now, restore the exact boundary only
          on a clean full replay (below). Leaving a stale synced_upto
          here would let a later fast-forward execute from a phantom
          position. *)
       e.synced_upto <- -1;
       let corr = Correlation.of_client "mcp-outline" in
       let st = Frame_stack.make () in
       let count = ref (fst (goals_info e.session)) in
       let sentences = ref [] in
       let obligations = ref [] in
       let admits = ref [] in
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
                 let adm =
                   if is_admit_sentence s then
                     match goals_info e.session with
                     | (_, sub :: _) ->
                       Some (one_line_concl sub, subgoal_hash sub)
                     | _ -> None
                   else None
                 in
                 let t0 = Unix.gettimeofday () in
                 (match
                    Ec_llm_session.exec e.session ~document:true
                      ~corr ~sentence_class:cls ~source:s.src
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
                    (match adm with
                     | Some (g1, h) ->
                       admits :=
                         `Assoc [
                           "path", `String path_before;
                           "start_line", `Int s.start_line;
                           "goal", `String g1;
                           "hash", `String h;
                         ] :: !admits
                     | None -> ());
                    count := n;
                    let kw = exec_keyword s.src in
                    (* Invocation-count, not leading-keyword: `by
                       smt(...)` closers inside have/selectors are
                       smt calls too (B14). *)
                    let smt_calls = count_keyword "smt" s.src in
                    let hint_max = smt_hint_max s.src in
                    sentences :=
                      `Assoc [
                        "path", `String path_before;
                        "src", `String s.src;
                        "time_ms", `Int (ms_since t0);
                        "goals_after", `Int n;
                        "closer",
                        `Bool (children = 0 || s.kind = "Gsave");
                        "smt", `Bool (smt_calls > 0);
                        "smt_calls", `Int smt_calls;
                        "smt_hint_max", `Int hint_max;
                        "admit", `Bool (kw = "admit");
                        "fragile",
                        `Bool
                          (kw = "progress"
                           || (String.length s.src > 0
                               && String.contains s.src '!')
                           || hint_max >= smt_hint_fragile_threshold);
                      ] :: !sentences))
            body
        with Exit -> ());
       (if !failed = None then
          match List.rev body with
          | last :: _ -> e.synced_upto <- last + 1
          | [] -> ());
       Ok
         (`Assoc [
            "lemma", `String lemma;
            "split_points", `Int !splits;
            "sentences", `List (List.rev !sentences);
            "obligations", `List (List.rev !obligations);
            "admitted", `List (List.rev !admits);
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
                 (* smt_count = INVOCATIONS (B14), not sentences
                    whose leading tactic is smt. *)
                 (match member "smt_calls" s with
                  | `Int k -> smt := !smt + k
                  | _ ->
                    if member "smt" s = `Bool true then incr smt);
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
            let total_smt_calls =
              List.fold_left
                (fun acc s ->
                   match member "smt_calls" s with
                   | `Int k -> acc + k
                   | _ -> acc)
                0 sentences
            in
            (* A proof with no real branching aggregates to one row,
               which is no resolution at all — fall back to the
               per-sentence table (src previews) so the hotspot is
               visible (B14). *)
            let flat =
              if List.length branches <= 1 then
                [ "sentences",
                  `List
                    (List.map
                       (fun s ->
                          `Assoc [
                            "src",
                            (match member "src" s with
                             | `String v -> `String (src_preview v)
                             | v -> v);
                            "time_ms", member "time_ms" s;
                            "smt_calls", member "smt_calls" s;
                            "smt_hint_max", member "smt_hint_max" s;
                            "admit", member "admit" s;
                            "fragile", member "fragile" s;
                          ])
                       sentences) ]
              else []
            in
            Ok (`Assoc ([
              "session", `String label;
              "lemma", `String lemma;
              "branches", `List branches;
            ] @ flat @ [
              "total_sentences", `Int (List.length sentences);
              "total_smt", `Int total_smt_calls;
              "total_admits", `Int (total "admit");
              "total_fragile", `Int (total "fragile");
              "split_points", member "split_points" payload;
              "admitted", member "admitted" payload;
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
       (match expand_defines e script with
        | Error m -> Error ("check_skeleton: " ^ m)
        | Ok (script, expanded) ->
       (match Ec_llm_session.parse_source e.session script with
        | Error err ->
          Error
            (Printf.sprintf "check_skeleton: script parse failed: %s"
               (Error.to_string err))
        | Ok (_, Some perr) ->
          Error
            (Printf.sprintf
               "check_skeleton: script has a parse error — nothing \
                ran: %s"
               perr)
        | Ok (ss, None) ->
          let start = Ec_llm_session.current_uuid e.session in
          let corr = Correlation.of_client "mcp-skeleton" in
          let detail = goal_detail_of args ~default:`Shape in
          let entry = entry_fields e.session in
          (match apply_smt_timeout e args ~corr with
           | Error m -> Error ("check_skeleton: " ^ m)
           | Ok applied ->
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
                    let is_hole = exec_keyword s.src = "admit" in
                    (if is_hole then
                       match goals_info e.session with
                       | (_, sub :: _) ->
                         holes :=
                           `Assoc [
                             "path", `String path;
                             "hash", `String (subgoal_hash sub);
                             "goal", apply_goal_detail detail sub;
                           ] :: !holes
                       | _ -> ());
                    (match
                       Ec_llm_session.exec e.session ~document:true
                         ~corr ~sentence_class:cls ~source:s.src
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
          ] @ entry @ [
            "holes", `List (List.rev !holes);
            "restore", restore;
            "uuid", `Int (Ec_llm_session.current_uuid e.session);
          ] @ smt_timeout_field applied
            @ src_expanded_field expanded script
            @ (match !failed with
               | None -> []
               | Some (s, er) ->
                 [ "error", `String er;
                   "goals_at_failure",
                   render_goals args ~detail !goals_fail;
                   "failed_at",
                   `Assoc [ "src", `String s.src ] ])))))))

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
          (match expand_defines e text with
           | Error m -> Error ("exec_in: " ^ m)
           | Ok (text, expanded) ->
          (match Ec_llm_session.parse_source e.session text with
           | Error err ->
             Error
               (Printf.sprintf "exec_in: parse failed: %s"
                  (Error.to_string err))
           | Ok (_, Some perr) ->
             Error
               (Printf.sprintf
                  "exec_in: input has a parse error — nothing ran: \
                   %s"
                  perr)
           | Ok (ss, None) ->
             (* Lexical gate: no proof closers (skeleton owner's
                business) and no focus-moving tactics — keyword-
                based, so a bulleted `+ cycle.` cannot slip the
                claim (B6 audit). *)
             let bad =
               List.find_opt
                 (fun (s : Ec_llm_session.parsed_sentence) ->
                    s.kind = "Gsave" || exec_keyword s.src = "cycle")
                 ss
             in
             (match bad with
              | Some s ->
                Error
                  (Printf.sprintf
                     "exec_in: '%s' is not allowed inside a claimed \
                      subtree (closers and cycle escape the claim)"
                     (src_preview s.src))
              | None ->
                let detail =
                  goal_detail_of args ~default:`Shape
                in
                let snapshot =
                  Ec_llm_session.current_uuid e.session
                in
                let corr = Correlation.of_client "mcp-execin" in
                let n_goals0 = fst (goals_info e.session) in
                let count = ref n_goals0 in
                let remaining = ref sc.sc_remaining in
                let executed = ref [] in
                let admitted = ref [] in
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
                     "admitted", `List (List.rev !admitted);
                     "uuid",
                     `Int (Ec_llm_session.current_uuid e.session);
                     "goals",
                     render_goals args ~detail (goals_json e.session);
                   ] @ tree_if_grew e.session ~before:n_goals0
                     @ src_expanded_field expanded text
                     @ (if sc.sc_closed then
                          [ "transcript",
                            `List
                              (List.rev_map
                                 (fun s -> `String s)
                                 sc.sc_transcript) ]
                        else [])))))))))

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
      ~upto_sentence:(int_arg args "upto_sentence")
      ~at_lemma:(str_arg args "at_lemma")
      ~goal_detail:(goal_detail_of args ~default:`Shape)

(* Verified in-place proof replacement: splice [script] over the
   claimed lemma's proof-body lines, resync (weak prefix +
   full-checked tail), and RESTORE the original file if
   verification fails. The first tool with write authority — gated
   on freshness (must resync first if the file changed
   out-of-band). *)
(* ---------------------------------------------------------------- *)
(* Verified landing — shared by replace_proof, check_script
   {on_close:"commit"} and commit_proof {write:true}.               *)
(* ---------------------------------------------------------------- *)

(* The session's claim on [lemma]: from the lock table in proof
   mode, resolved on demand in statement mode. *)
let claim_for (e : entry) label lemma =
  match e.mode with
  | Proof cs ->
    (match List.find_opt (fun c -> c.lemma = lemma) cs with
     | Some c -> Ok c
     | None ->
       Error
         (Printf.sprintf
            "lemma '%s' is not claimed by session '%s' (claims: %s)"
            lemma label
            (String.concat ", " (claim_names e.mode))))
  | Statement ->
    (match resolve_claims e.parsed [ lemma ] with
     | Ok [ c ] -> Ok c
     | Ok _ -> Error "internal claim resolution shape"
     | Error m -> Error m)

(* The at_lemma position (sentence count through the declaration and
   its `proof.`) for [lemma] against the current snapshot — the
   position from which a checked script IS the full proof body. *)
let lemma_start_target (e : entry) lemma =
  match resolve_claims e.parsed [ lemma ] with
  | Error m -> Error m
  | Ok [ c ] ->
    let d = ref (-1) in
    Array.iteri
      (fun i (s : Ec_llm_session.parsed_sentence) ->
         if !d = -1 && s.kind = "Gaxiom" && s.start_line = c.start_line
         then d := i)
      e.parsed;
    if !d < 0 then Error "declaration not found in snapshot"
    else
      let m = !d + 1 in
      let m =
        if m < Array.length e.parsed
           && exec_keyword
                (e.parsed.(m) : Ec_llm_session.parsed_sentence).src
              = "proof"
        then m + 1
        else m
      in
      Ok (c, m)
  | Ok _ -> Error "internal claim resolution shape"

(* Wrap a body fragment into a full, file-ready proof body: prepend
   `proof.` unless present, append `qed.` unless a save is present.
   Always followed by verified execution, so a wrong wrap fails
   loudly and restores. *)
let wrap_proof_body (body : string) =
  let body = String.trim body in
  let s =
    if exec_keyword body = "proof" then body
    else "proof.\n" ^ body
  in
  let has_save =
    List.exists
      (fun l ->
         let kw = exec_keyword l in
         kw = "qed" || kw = "save")
      (String.split_on_char '\n' s)
  in
  if has_save then s else s ^ "\nqed."

(* Splice [script] over [c]'s body lines, resync-verify (weak prefix
   + fully-checked tail), RESTORE the original file if verification
   fails. Returns (verified, resync payload). *)
let write_body_verified ~label (e : entry) (c : claim) ~script ~nosmt =
  let orig = e.text in
  let lines = String.split_on_char '\n' orig in
  let pre = List.filteri (fun i _ -> i < c.decl_end_line) lines in
  let post = List.filteri (fun i _ -> i >= c.end_line) lines in
  let script_lines = String.split_on_char '\n' (String.trim script) in
  let candidate = String.concat "\n" (pre @ script_lines @ post) in
  let resync () =
    resync_impl ~label e ~nosmt ~upto_line:None ~upto_sentence:None
      ~at_lemma:None ~goal_detail:`Shape
  in
  match write_file e.file candidate with
  | exception Sys_error m -> Error (Printf.sprintf "write failed: %s" m)
  | () ->
    (match resync () with
     | Error m ->
       (try write_file e.file orig with _ -> ());
       ignore (resync ());
       Error
         (Printf.sprintf
            "verification could not run (%s); file restored" m)
     | Ok payload ->
       let ok =
         match Yojson.Safe.Util.member "ok" payload with
         | `Bool b -> b
         | _ -> false
       in
       if ok then Ok (true, payload)
       else begin
         (try write_file e.file orig with _ -> ());
         ignore (resync ());
         Ok (false, payload)
       end)

let tool_commit_proof t args =
  match find_session t args with
  | Error e -> Error e
  | Ok (label, e) ->
    (match Ec_llm_session.raw_command e.session "COMMIT" with
     | Error err -> Error (Error.to_string err)
     | Ok (body, _) ->
       let empty = String.trim body = "" in
       let empty_reason =
         "the authoring transcript is empty — it records only \
          phrases YOU executed since this proof was opened \
          (positioning replays don't count, and any resync/LOAD \
          clears it)"
       in
       if not (bool_arg args "write") then
         Ok (`Assoc ([
           "session", `String label;
           "stale", `Bool (stale_flag e);
           "proof", `String body;
         ] @ (if empty then [ "note", `String empty_reason ]
              else [])))
       else
         (* Zero-seam ending for the step loop: transcript ->
            wrapped body -> verified in-place write. *)
         (match str_arg args "lemma" with
          | None ->
            Error "commit_proof: write=true requires 'lemma'"
          | Some lemma ->
            if empty then
              Error
                ("commit_proof: nothing to land — " ^ empty_reason
                 ^ "; re-step the proof, or land composed text \
                    with replace_proof")
            else if stale_flag e then
              Error
                "commit_proof: file changed on disk — resync_file \
                 first"
            else if not (goals_closed e.session) then
              Error
                "commit_proof: the proof is not closed — keep \
                 going, or land a partial body explicitly with \
                 replace_proof"
            else
              (match claim_for e label lemma with
               | Error m -> Error ("commit_proof: " ^ m)
               | Ok c ->
                 let script = wrap_proof_body body in
                 let nosmt =
                   match Yojson.Safe.Util.member "nosmt" args with
                   | `Bool b -> b
                   | _ -> true
                 in
                 (match
                    write_body_verified ~label e c ~script ~nosmt
                  with
                  | Error m -> Error ("commit_proof: " ^ m)
                  | Ok (okv, payload) ->
                    Ok (`Assoc [
                      "ok", `Bool okv;
                      "lemma", `String lemma;
                      (if okv then "file_written"
                       else "file_restored"),
                      `Bool true;
                      "proof", `String script;
                      "verification", payload;
                    ])))))


let tool_check_script t args =
  match str_arg args "script" with
  | None -> Error "check_script: missing required argument 'script'"
  | Some script ->
    (match find_session t args with
     | Error e -> Error e
     | Ok (label, e) ->
       (match expand_defines e script with
        | Error m -> Error ("check_script: " ^ m)
        | Ok (script, expanded) ->
       (match Ec_llm_session.parse_source e.session script with
        | Error err ->
          Error
            (Printf.sprintf "check_script: script parse failed: %s"
               (Error.to_string err))
        | Ok (_, Some perr) ->
          Error
            (Printf.sprintf
               "check_script: script has a parse error — nothing \
                ran: %s"
               perr)
        | Ok (ss, None) ->
          let start = Ec_llm_session.current_uuid e.session in
          let corr = Correlation.of_client "mcp-check" in
          let detail = goal_detail_of args ~default:`Shape in
          let entry = entry_fields e.session in
          (match apply_smt_timeout e args ~corr with
           | Error m -> Error ("check_script: " ^ m)
           | Ok applied ->
          let admitted = ref [] in
          let results = ref [] in
          let failed = ref false in
          let goals_fail = ref `Null in
          let restarted = ref false in
          let n_goals0 = fst (goals_info e.session) in
          let t0 = Unix.gettimeofday () in
          (try
             List.iteri
               (fun i (s : Ec_llm_session.parsed_sentence) ->
                  match sentence_class_of s with
                  | None -> ()
                  | Some cls ->
                    let s0 = Unix.gettimeofday () in
                    let adm =
                      if is_admit_sentence s then
                        capture_admit e.session detail
                      else None
                    in
                    (* Candidate bodies are DOCUMENT text: they are
                       destined for the file verbatim, so they are
                       checked under the file's own rules — strict
                       bullets included (B7 parity: what passes here
                       is what lands and compiles). *)
                    (match
                       Ec_llm_session.exec e.session ~document:true
                         ~corr ~sentence_class:cls ~source:s.src
                     with
                     | Ok ok ->
                       if ok.restarted then begin
                         restarted := true;
                         raise Exit
                       end;
                       (match adm with
                        | Some (g, h) ->
                          admitted :=
                            `Assoc [
                              "index", `Int i;
                              "src", `String (src_preview s.src);
                              "goal", g;
                              "hash", `String h;
                            ] :: !admitted
                        | None -> ());
                       results :=
                         `Assoc [
                           "index", `Int i;
                           "src", `String (src_preview s.src);
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
          (* Captured before any restore below. *)
          let tree_extra =
            if !failed || !restarted then []
            else tree_if_grew e.session ~before:n_goals0
          in
          let revert_to_start () =
            if Ec_llm_session.current_uuid e.session = start then
              `String "unmoved"
            else
              match
                Ec_llm_session.revert_to_uuid e.session ~target:start
              with
              | Ok () -> `String "restored"
              | Error er ->
                `String ("RESTORE FAILED: " ^ Error.to_string er)
          in
          (* Landing switch (ergonomics): the iterate call is also
             the landing call. on_close = restore (default) | keep
             (state stays advanced) | commit (verified in-place
             write of the full body — requires a claimed lemma and
             the at_lemma position, so the checked script IS the
             whole body). *)
          let do_commit () =
            match str_arg args "lemma" with
            | None -> Error "on_close=commit requires 'lemma'"
            | Some lemma ->
              (match claim_for e label lemma with
               | Error m -> Error m
               | Ok c ->
                 (match lemma_start_target e lemma with
                  | Error m -> Error m
                  | Ok (_, m_target) ->
                    if e.synced_upto <> m_target then
                      Error
                        (Printf.sprintf
                           "session is not at %s's proof start — \
                            resync_file {at_lemma: \"%s\"} first, \
                            then re-check"
                           lemma lemma)
                    else begin
                      let script =
                        wrap_proof_body script
                      in
                      (* The session is mid-flight here — advanced
                         past the candidate, not yet reverted — so
                         its recorded file-prefix position is NOT
                         current. Invalidate before the verified
                         write: the resync inside re-establishes an
                         honest position on every exit path. *)
                      e.synced_upto <- -1;
                      (match
                         write_body_verified ~label e c ~script
                           ~nosmt:true
                       with
                       | Error m -> Error m
                       | Ok (true, payload) ->
                         Ok [ "file_written", `Bool true;
                              "verification", payload ]
                       | Ok (false, payload) ->
                         Ok [ "file_restored", `Bool true;
                              "verification", payload ])
                    end))
          in
          let on_close =
            match str_arg args "on_close" with
            | Some "keep" -> `Keep
            | Some "commit" -> `Commit
            | _ -> `Restore
          in
          let (restore, commit_fields) =
            if !restarted then
              (`String
                 "session restarted mid-script — state NOT \
                  restored; run resync_file to recover",
               [])
            else
              match on_close, closes with
              | `Keep, true ->
                e.synced_upto <- -1;
                (`String "kept",
                 (match applied with
                  | Some n ->
                    [ "note",
                      `String
                        (Printf.sprintf
                           "on_close=keep retains the transactional \
                            smt_timeout — the kept state has \
                            `timeout %d.` applied; exec a new \
                            `timeout N.` to change it" n) ]
                  | None -> []))
              | `Commit, true ->
                (match do_commit () with
                 | Ok fields -> (`String "committed", fields)
                 | Error msg ->
                   let r = revert_to_start () in
                   (r, [ "commit_error", `String msg ]))
              | _ -> (revert_to_start (), [])
          in
          Ok (`Assoc ([
            "session", `String label;
            "checked", `Int (List.length !results);
            "ok", `Bool ((not !failed) && not !restarted);
            "closes", `Bool closes;
          ] @ entry @ [
            "results", `List (List.rev !results);
            "admitted", `List (List.rev !admitted);
            "restore", restore;
            "uuid", `Int (Ec_llm_session.current_uuid e.session);
            "total_time_ms", `Int (ms_since t0);
            "stale", `Bool (stale_flag e);
          ] @ smt_timeout_field applied
            @ src_expanded_field expanded script
            @ commit_fields
            @ (if !failed then
                 [ "goals_at_failure",
                   render_goals args ~detail !goals_fail ]
               else
                 [ "goals_at_end",
                   render_goals args ~detail goals_at_end ]
                 @ tree_extra)))))))


let tool_replace_proof t args =
  match str_arg args "lemma", str_arg args "script" with
  | None, _ -> Error "replace_proof: missing required argument 'lemma'"
  | _, None -> Error "replace_proof: missing required argument 'script'"
  | Some lemma, Some script ->
    (match find_session t args with
     | Error e -> Error e
     | Ok (label, e) ->
       (match expand_defines e script with
        | Error m -> Error ("replace_proof: " ^ m)
        | Ok (script, s_expanded) ->
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
                 (match resync_impl ~label e ~nosmt ~upto_line:None ~upto_sentence:None ~at_lemma:None ~goal_detail:`Shape with
                  | Error m ->
                    (try write_file e.file orig with _ -> ());
                    ignore
                      (resync_impl ~label e ~nosmt ~upto_line:None ~upto_sentence:None ~at_lemma:None ~goal_detail:`Shape);
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
                      Ok (`Assoc ([
                        "ok", `Bool true;
                        "lemma", `String lemma;
                        "replaced_lines",
                        `Assoc [
                          "from", `Int (c.decl_end_line + 1);
                          "to", `Int c.end_line;
                        ];
                        "file_written", `Bool true;
                        "verification", payload;
                      ] @ src_expanded_field s_expanded script))
                    else begin
                      (try write_file e.file orig with _ -> ());
                      ignore
                        (resync_impl ~label e ~nosmt ~upto_line:None ~upto_sentence:None ~at_lemma:None ~goal_detail:`Shape);
                      Ok (`Assoc ([
                        "ok", `Bool false;
                        "lemma", `String lemma;
                        "file_restored", `Bool true;
                        "verification", payload;
                      ] @ src_expanded_field s_expanded script))
                    end))
            end)))

(* File-level admit audit: the goals your admits close. Scans the
   snapshot for declarations whose bodies contain admit sentences
   and replays each through the outline engine (weak-checked
   prefix). REPOSITIONS the session like proof_outline; scope with
   'lemma' on big files (no cancellation yet). *)
let tool_admitted_goals t args =
  match find_session t args with
  | Error e -> Error e
  | Ok (label, e) ->
    if stale_flag e then
      Error "admitted_goals: file changed on disk — resync_file first"
    else
      let targets =
        match str_arg args "lemma" with
        | Some l -> [ l ]
        | None ->
          let cur = ref None in
          let out = ref [] in
          Array.iter
            (fun (s : Ec_llm_session.parsed_sentence) ->
               (if s.kind = "Gaxiom" then
                  match s.name with
                  | Some n -> cur := Some n
                  | None -> ());
               if is_admit_sentence s then
                 match !cur with
                 | Some n when not (List.mem n !out) ->
                   out := n :: !out
                 | _ -> ())
            e.parsed;
          List.rev !out
      in
      let admits = ref [] in
      let errors = ref [] in
      List.iter
        (fun lemma ->
           match outline_engine e lemma with
           | Error m ->
             errors :=
               `Assoc [ "lemma", `String lemma; "error", `String m ]
               :: !errors
           | Ok (payload, failed) ->
             (match failed with
              | Some (_, er) ->
                errors :=
                  `Assoc [ "lemma", `String lemma;
                           "error", `String er ] :: !errors
              | None -> ());
             (match Yojson.Safe.Util.member "admitted" payload with
              | `List l ->
                List.iter
                  (fun a ->
                     match a with
                     | `Assoc kvs ->
                       admits :=
                         `Assoc (("lemma", `String lemma) :: kvs)
                         :: !admits
                     | _ -> ())
                  l
              | _ -> ()))
        targets;
      Ok (`Assoc [
        "session", `String label;
        "lemmas_scanned",
        `List (List.map (fun l -> `String l) targets);
        "admit_count", `Int (List.length !admits);
        "admitted", `List (List.rev !admits);
        "errors", `List (List.rev !errors);
        "note",
        `String
          "session repositioned by the replay — resync_file \
           {at_lemma} to reposition";
      ])

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

let goal_detail_prop =
  ("goal_detail", "string",
   "Goal payload size: \"full\" | \"shape\" (program bodies elided \
    to instruction counts) | \"counts\" (subgoal count + one-line \
    conclusions). Defaults: full on goals, shape on try_tactic and \
    the loop tools.")

let smt_timeout_prop =
  ("smt_timeout", "integer",
   "Transactional prover timeout in seconds for THIS call only — \
    fail fast while exploring (1), let a believed-good candidate \
    run long (30). Restored with the state when the call ends. \
    Persistent variant: exec {text: \"timeout N.\"}.")

let goal_scope_prop =
  ("goal_scope", "string",
   "WHICH goals the payload carries (orthogonal to goal_detail): \
    \"all\" (default) or \"focused\" — only the focused subgoal, \
    with subgoal_count still reporting the true total. On a \
    20-goal call-dispatch state this is one goal instead of 80 kB.")

let max_chars_prop =
  ("max_chars", "integer",
   "Hard cap on each pretty-printed formula in goal payloads \
    (UTF-8-safe, trailing … marks the cut). The third size axis: \
    goal_scope picks WHICH goals, goal_detail HOW MUCH structure, \
    max_chars how much FORMULA text — up-to-bad conclusions \
    duplicate whole invariants and dwarf everything else.")

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
  "Execute EasyCrypt input in the session, advancing its state. \
   Multi-sentence input is split by the real parser and executed \
   ONE SENTENCE AT A TIME: successes COMMIT, the first failure \
   stops the sequence, and the reply reports every sentence \
   (per-sentence uuid and time_ms; goals_at_failure on error — \
   sentences before the failure REMAIN EXECUTED). When the call \
   GROWS the open-goal count the reply carries the compact `tree` \
   (one line per goal) so the new subgoal ORDER is visible without \
   a round trip. $name references expand from this session's \
   `define` bindings (reply echoes src_expanded).",
  schema ~required:[ "text" ] [
    ("text", "string", "EasyCrypt source to execute.");
    goal_scope_prop;
    max_chars_prop;
    goal_detail_prop;
    session_prop;
  ],
  tool_exec;

  "define",
  "Bind a name on the session: $name in the EC-bound inputs of \
   exec / exec_in / query / try_tactic / check_script / \
   check_skeleton / replace_proof expands to the bound text before \
   parsing — send a six-line invariant ONCE, reference it \
   everywhere. Purely lexical, single-pass (a define's text may \
   not reference defines), unknown $names are hard errors, and \
   whenever expansion changed an input the reply echoes the full \
   expanded source as src_expanded — the transcript always shows \
   exactly what ran, and files only ever receive expanded EC. \
   {name, text} sets, {name} alone deletes, no name lists; the \
   reply always carries the session's full binding table.",
  schema [
    ("name", "string",
     "Binding name ([A-Za-z_][A-Za-z0-9_']*). Omit to just list \
      the current bindings.");
    ("text", "string",
     "EC text to bind. Omit to DELETE the named binding.");
    session_prop;
  ],
  tool_define;

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
  schema [ goal_scope_prop; max_chars_prop; goal_detail_prop; session_prop ],
  tool_goals;

  "tree",
  "Render the open-subgoal tree with dotted-path labels (matching \
   what focus accepts) and the focused goal marked. Line ORDER is \
   STRUCTURAL (siblings grouped under their split frame), not the \
   subgoal order — each line's #N annotation is the order \
   authority: the 0-based index into GOALS-JSON's subgoals array \
   and the focus rotation sequence. Plan bullet skeletons from the \
   #N indices; read the tree for shape.",
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
   exec. Replies default to goal_detail=shape; a goal-count \
   increase attaches the compact `tree` (captured before the \
   revert).",
  schema ~required:[ "tactic" ] [
    ("tactic", "string", "Tactic source, '.'-terminated.");
    goal_scope_prop;
    max_chars_prop;
    smt_timeout_prop;
    goal_detail_prop;
    session_prop;
  ],
  tool_try_tactic;

  "try_script",
  "Multi-sentence STATE-NEUTRAL probe: run a short authored \
   sequence from the current state, get per-sentence verdicts and \
   the resulting goals, then the state is ALWAYS restored — \
   exec+revert as one atomic call. Use it for \"what do these \
   sentences do here\": exec would COMMIT the probe (poisoning \
   later check_scripts), and check_script is the document-rules \
   candidate checker, not a probe. Replies carry the same entry \
   field, previews, auto-tree and payload knobs as check_script.",
  schema ~required:[ "script" ] [
    ("script", "string",
     "Sentences ('.'-terminated, newline-separated) to probe.");
    goal_scope_prop;
    max_chars_prop;
    smt_timeout_prop;
    goal_detail_prop;
    session_prop;
  ],
  tool_try_script;

  "check_script",
  "Speculatively run a multi-sentence candidate script (e.g. a \
   whole replacement proof body) from the current state: executes \
   sentence-by-sentence until the first failure, reports per-\
   sentence verdicts + timings and whether the proof CLOSES, then \
   restores the session to where it was. The refactoring inner \
   loop: iterate candidates here without touching the file, write \
   once with replace_proof when one passes. Candidates are checked \
   as DOCUMENT text FROM THE CURRENT STATE — the reply's `entry` \
   field says exactly what that was (focused goal one-liner, open \
   count, bullet stack depth). Land-parity for a WHOLE-BODY \
   candidate therefore needs the lemma's proof-start position \
   (resync_file {at_lemma}; bullet depth 0) — mid-proof, the live \
   bullet stack applies and the reply says so. The restore also \
   means a SUFFIX-only retry re-runs from the same entry state \
   (send the full body, or exec the verified prefix and probe with \
   try_tactic), and the focus NEVER advances here — bullet-\
   consuming scripts that should move you forward belong in exec. \
   Per-sentence rows echo a one-line src PREVIEW (full source on \
   the failing sentence); a net goal-count increase attaches the \
   compact `tree`.",
  schema ~required:[ "script" ] [
    ("script", "string",
     "EasyCrypt sentences ('.'-terminated, newline-separated), \
      e.g. \"proof.\\nsplit.\\ntrivial.\\nqed.\"");
    goal_scope_prop;
    max_chars_prop;
    smt_timeout_prop;
    goal_detail_prop;
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
    goal_scope_prop;
    max_chars_prop;
    smt_timeout_prop;
    goal_detail_prop;
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
   sentence counts, time, smt/admit counts, fragility markers. \
   smt_count counts INVOCATIONS — `by smt(...)` closers inside \
   have/selector sentences included, anywhere in the sentence. \
   Fragile = progress, !-rewrites, or an smt hint list of 8+ \
   lemmas (per-sentence smt_hint_max reported). A proof with <= 1 \
   branch also carries the per-sentence table (src preview + \
   time_ms + smt_calls) — bullet-free proofs get per-sentence \
   resolution instead of one opaque row. Same replay as \
   proof_outline (repositions the session); use it to decide WHAT \
   is worth restructuring before deciding how.",
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
    goal_scope_prop;
    max_chars_prop;
    goal_detail_prop;
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

  "admitted_goals",
  "The goals your admits close: scans for admit-bearing \
   declarations and replays them (weak prefix) to capture each \
   admitted goal + hash. Every executing tool also reports a live \
   'admitted' array; this is the whole-file audit. Repositions \
   the session. Scope with 'lemma' on big files.",
  schema [
    ("lemma", "string",
     "Audit only this declaration (default: every admit-bearing \
      one).");
    session_prop;
  ],
  tool_admitted_goals;

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
   bullet-structured proof body — the bridge from session-first \
   exploration back into text. The transcript is PER-PROOF and \
   authoring-only: phrases YOU executed since the current proof \
   opened (typed bullets are stripped — COMMIT owns bullet \
   presentation, valid under strict_bullets); positioning replays \
   never count and any resync/LOAD clears it. With write:true AND \
   a claimed lemma, LANDS the proof directly: wraps the transcript \
   in proof./qed., splices it over the lemma's body, \
   resync-verifies, and restores the file on failure. Requires \
   the proof to be CLOSED; an empty transcript refuses to land. \
   The zero-seam ending for the step loop.",
  schema [
    ("lemma", "string",
     "Required with write:true — the claimed lemma to land into.");
    ("write", "boolean",
     "Verified in-place write of the transcript body. Default \
      false (text is only returned).");
    ("nosmt", "boolean",
     "Weak-check the unchanged prefix during write verification \
      (default true).");
    session_prop;
  ],
  tool_commit_proof;

  "resync_file",
  "Re-sync the session with its (edited) file incrementally: diffs \
   the new text against the loaded snapshot (comment-blind — a \
   comment/whitespace-only edit classifies formatting-only, swaps \
   the snapshot and PRESERVES the session position, state and \
   claims at zero cost), weak-checks the unchanged prefix (nosmt, \
   default true), then FULL-checks the changed tail sentence-by-\
   sentence. Reports the edit classification. proof-body-only \
   carries an environment-equivalence certificate (every changed \
   sentence is a proof tactic, save outcomes preserved), so the \
   unchanged tail BELOW the edit is skipped (tail_skipped) and the \
   session lands at the edited lemma's end — resync again or hop \
   forward to load more; statement-changing edits re-check \
   everything downstream and are warned in proof mode. Run this \
   after ANY on-disk edit (replies carry stale=true until you do). \
   Note: on any executing resync the session state becomes exactly \
   the file's state; interactive work not in the file is dropped.",
  schema [
    ("nosmt", "boolean",
     "Weak-check the unchanged prefix (default TRUE — the changed \
      tail is always fully checked).");
    ("upto_line", "integer",
     "Re-sync only up to this line (repositioning). Default: whole \
      file.");
    ("upto_sentence", "integer",
     "Execute exactly the first N sentences (sentence-granular \
      positioning at ANY boundary, incl. mid packed line); indices \
      match analyze_file\x27s sentence order and the reply\x27s \
      target_sentences.");
    ("at_lemma", "string",
     "Position just inside this lemma's proof (after its proof. \
      sentence) — sentence-granular, works on packed lines where \
      upto_line cannot.");
    goal_detail_prop;
    session_prop;
  ],
  tool_resync_file;

  "replace_proof",
  "Verified in-place proof replacement — the refactoring commit \
   step. Splices 'script' over the claimed lemma's proof-body \
   lines, re-syncs (weak prefix, fully-checked spliced body under \
   the file's OWN rules — strict_bullets included; the unchanged \
   tail below is certificate-skipped, not re-verified), and \
   RESTORES the original file automatically if verification \
   fails. Requires freshness (resync_file first if the file \
   changed out-of-band) and, in proof mode, a claim on the lemma. \
   $name references expand from `define` bindings (code only — \
   comments/strings untouched) — the file receives expanded EC.",
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
   classes and enclosing-scope tags. Use view=\"triage\" for the \
   mass-restatement question — first diagnostic per enclosing \
   declaration with cascades counted (201 diagnostics are usually \
   a handful of root causes); \"diagnostics\" drops the sentence \
   inventory; \"full\" (default) is the complete dump.",
  schema ~required:[ "path" ] [
    ("path", "string", "Path to the .ec/.eca file to analyze.");
    ("view", "string",
     "\"full\" (default) | \"diagnostics\" (errors only) | \
      \"triage\" (FIRST error per enclosing declaration + \
      suppressed-cascade counts — the readable view of a broken \
      big file).");
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
          stale=true until you do. Two landing paths, both \
          self-writing: check_script {on_close:\"commit\", lemma} \
          lands a passing body in the same call; or step with exec \
          (watch for proof_complete:true) and land with \
          commit_proof {lemma, write:true}.";
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
