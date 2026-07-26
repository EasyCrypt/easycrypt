(** Shared interactive state + command handlers used by both the
    line REPL (`ecd repl`) and the TUI (`ecd tui`). Per the TUI/REPL
    parity rule: no command lives in only one frontend.

    Output is routed through the [out] callback in [state] so the
    line REPL can print immediately and the TUI can capture messages
    into a scroll-buffer for its log pane. *)

(* Sibling modules of [Repl_core] inside the [ecd_core] library
   (Ec_llm_session, Document, Sentence_id, Error, Transcript,
   Correlation) are reachable without a qualifier. *)

type state = {
  mutable session  : Ec_llm_session.t;
  mutable doc      : Document.t option;
  mutable executed : Document.sentence list;
  sw               : Eio.Switch.t;
  mutable out      : string -> unit;
  (** Sink for status / log lines (no trailing newline). Default:
      [print_endline]. TUI routes these into its log pane. *)
  mutable result   : string -> unit;
  (** Sink for directive reply bodies (`print`, `search`, `locate`,
      `pragma`). Only fired for class `Directive` — executable
      sentences' reply bodies echo the goal state and belong in
      the goals pane, not here. Default: same as [out]. *)
  mutable clear_result : unit -> unit;
  (** Called by state-mutating commands (:step, :back, :reload,
      :restart, and :feed of non-directive sentences) to drop stale
      directive output. Default: no-op; the TUI empties its result
      buffer. *)
  mutable goal_cursor : int;
  (** 0-based index into the current [subgoals] array, selecting
      which goal [cmd_goals] renders. 0 is EC's focused goal; any
      higher index is a lookahead view. Reset to 0 on every
      state-mutating command. *)
  mutable disk_source : string;
  (** Last content we synced with the file on disk. [doc.source] is
      the in-memory buffer that :insert / :edit / :delete modify;
      :save writes the buffer out and updates this. :diff compares
      them. Empty when no doc is loaded. *)
}

let make ~session ~sw =
  { session; doc = None; executed = []; sw;
    out = print_endline;
    result = print_endline;
    clear_result = (fun () -> ());
    goal_cursor = 0;
    disk_source = "" }

let emit st fmt = Printf.ksprintf st.out fmt

let read_file path =
  let ic = open_in path in
  let n  = in_channel_length ic in
  let s  = really_input_string ic n in
  close_in ic;
  s

(* Respawn a fresh subprocess session. Used by :restart when the
   current one is dead and as the fallback recovery from any
   Session_restarted result. Drops the executed cursor since the new
   session knows nothing of what was already fed. *)
let respawn_session st =
  (try Ec_llm_session.close st.session with _ -> ());
  st.session <- Ec_llm_session.start ~sw:st.sw ~label:"repl";
  st.executed <- []

let cls_of (p : Ec_llm_session.parsed_sentence)
  : [ `Executable | `Doc_comment | `Directive ] =
  match p.cls with
  | `Executable  -> `Executable
  | `Doc_comment -> `Doc_comment
  | `Directive   -> `Directive
  | `Meta -> assert false

let cls_string = function
  | `Executable  -> "executable"
  | `Doc_comment -> "doc_comment"
  | `Directive   -> "directive"

let emit_result st s =
  if s <> "" then
    List.iter st.result (String.split_on_char '\n' s)

let exec_with_recovery st ~cls ~kind ~src =
  let corr = Correlation.of_client "repl-feed" in
  match
    Ec_llm_session.exec st.session ~corr ~sentence_class:cls ~source:src
  with
  | Ok ok ->
    emit st "[%-11s %-14s uuid=%d]  %s"
      (cls_string cls) kind ok.replied_uuid
      (if ok.restarted then "[restarted]" else "");
    List.iter (fun n -> emit st "  NOTICE: %s" n) ok.notices;
    (* Only directives (print/search/locate/pragma) produce reply
       bodies that carry user-facing query results. Executable
       sentences' reply bodies echo the post-step goals, which the
       goals pane already shows — emitting those to result pollutes
       the pane. *)
    if cls = `Directive then emit_result st ok.output;
    if ok.restarted then st.executed <- [];
    `Ok
  | Error (Error.Session_restarted { reason }) ->
    emit st "session died (%s); respawning…" reason;
    respawn_session st;
    `Respawned
  | Error e ->
    emit st "feed: %s" (Error.to_string e);
    `Err

(* --- Commands ------------------------------------------------------ *)

let cmd_pos st =
  match st.doc with
  | None -> emit st "no document loaded"
  | Some d ->
    let total  = List.length d.sentences in
    let cursor = List.length st.executed in
    let sid =
      match st.executed with
      | [] -> "<start>"
      | sn :: _ -> Sentence_id.to_string sn.id
    in
    emit st "[%d/%d  sid=%s]" cursor total sid

let cmd_step st n =
  st.clear_result ();
  st.goal_cursor <- 0;
  match st.doc with
  | None -> emit st "no document loaded"
  | Some d ->
    let cursor = List.length st.executed in
    let remaining =
      List.filteri (fun i _ -> i >= cursor) d.sentences
      |> List.filter (fun (sn : Document.sentence) -> sn.parsed.cls <> `Meta)
    in
    let rec go k = function
      | _ when k <= 0 -> ()
      | [] -> emit st "at end of document"
      | (sn : Document.sentence) :: rest ->
        match
          exec_with_recovery st ~cls:(cls_of sn.parsed)
            ~kind:sn.parsed.kind ~src:sn.parsed.src
        with
        | `Ok ->
          st.executed <- sn :: st.executed;
          go (k - 1) rest
        | `Respawned | `Err -> ()
    in
    go n remaining

let cmd_back st n =
  st.clear_result ();
  st.goal_cursor <- 0;
  if n < 1 then ()
  else match st.executed with
    | [] -> emit st "nothing executed"
    | _ ->
      let rec drop k xs =
        if k <= 0 then xs
        else match xs with [] -> [] | _ :: t -> drop (k - 1) t
      in
      let target_rest = drop n st.executed in
      match target_rest with
      | [] ->
        emit st "cannot revert before first sentence; use :restart instead"
      | target :: _ ->
        (match Ec_llm_session.revert_to st.session target.id with
         | Ok () ->
           st.executed <- target_rest;
           emit st "reverted to %s" (Sentence_id.to_string target.id)
         | Error e ->
           emit st "revert failed: %s" (Error.to_string e))

(* Render the subgoal at [goal_cursor] as a pretty multi-line block.
   Queries GOALS-JSON (addition 3), parses the subgoals array, clamps
   the cursor against the array length, formats hypotheses + a rule
   + the conclusion, and prepends a one-line header of the form
     `Goal i/N [focused|lookahead]`
   where "focused" is the 0-th subgoal (EC's focus). Returns a ready-
   to-print string; errors become human-readable single-line fallbacks. *)
let focused_goal_text st =
  match Ec_llm_session.goals ~structured:true st.session with
  | Error e -> "goals: " ^ Error.to_string e
  | Ok s ->
    match Yojson.Safe.from_string s with
    | exception _ -> "goals: malformed JSON"
    | json ->
      let open Yojson.Safe.Util in
      (try
         let active = json |> member "active" |> to_bool in
         if not active then "(no active goal)"
         else begin
           let subgoals = json |> member "subgoals" |> to_list in
           let count = List.length subgoals in
           let current_index =
             try json |> member "current_index" |> to_int
             with _ -> 0
           in
           if count = 0 then "(no subgoals)"
           else
             let i = max 0 (min (count - 1) st.goal_cursor) in
             let g = List.nth subgoals i in
             let hyps = g |> member "hypotheses" |> to_list in
             let concl =
               (* UPSTREAM #23: conclusion is now a structured tree
                  rather than a flat string. Decode via Goal_view +
                  flatten back to text for the REPL view. *)
               match member "conclusion" g with
               | `Null -> "(no conclusion)"
               | sub ->
                 (try Goal_view.to_pp_text (Goal_view.decode_conclusion sub)
                  with _ -> "(no conclusion)")
             in
             let hyp_line h =
               let name = try h |> member "name" |> to_string with _ -> "?" in
               let pp = try h |> member "pp" |> to_string with _ -> "" in
               Printf.sprintf "  %s: %s" name pp
             in
             let header =
               Printf.sprintf "Goal %d/%d [%s]"
                 (i + 1) count
                 (if i = current_index then "focused" else "lookahead")
             in
             String.concat "\n"
               (header
                :: List.map hyp_line hyps
                @ [ "------------------------------------------------------------"
                  ; concl ])
         end
       with Type_error (msg, _) -> "goals: JSON shape: " ^ msg
          | _ -> "goals: unparseable")

(* Default :goals renders the focused-goal block (see
   [focused_goal_text]). For rarer needs there are two explicit
   variants: [:goals json] dumps the raw GOALS-JSON for tools, and
   [:goals plain] prints EC's pretty GOALS output (all hypotheses
   of the focused subgoal only, with EC's own formatting). *)
type goals_mode = [ `Focused | `Json | `Plain ]

let cmd_goals ?(mode : goals_mode = `Focused) st =
  match mode with
  | `Focused ->
    List.iter st.out (String.split_on_char '\n' (focused_goal_text st))
  | `Json ->
    (match Ec_llm_session.goals ~structured:true st.session with
     | Ok s    -> List.iter st.out (String.split_on_char '\n' s)
     | Error e -> emit st "goals: %s" (Error.to_string e))
  | `Plain ->
    (match Ec_llm_session.goals ~structured:false st.session with
     | Ok s    -> List.iter st.out (String.split_on_char '\n' s)
     | Error e -> emit st "goals: %s" (Error.to_string e))

(* Peek at the subgoal count so :next-goal / :prev-goal can clamp
   properly. Returns [None] on any parse problem. *)
let subgoal_count st =
  match Ec_llm_session.goals ~structured:true st.session with
  | Error _ -> None
  | Ok s ->
    match Yojson.Safe.from_string s with
    | exception _ -> None
    | json ->
      let open Yojson.Safe.Util in
      try
        if json |> member "active" |> to_bool then
          Some (List.length (json |> member "subgoals" |> to_list))
        else Some 0
      with _ -> None

let cmd_next_goal st =
  (match subgoal_count st with
   | None | Some 0 -> emit st "no subgoals"
   | Some count ->
     let next = min (count - 1) (st.goal_cursor + 1) in
     if next = st.goal_cursor then emit st "already at last subgoal"
     else begin
       st.goal_cursor <- next;
       cmd_goals st
     end)

let cmd_prev_goal st =
  if st.goal_cursor <= 0 then emit st "already at first subgoal"
  else begin
    st.goal_cursor <- st.goal_cursor - 1;
    cmd_goals st
  end

(* Read-only one-shot: only executes sentences EC classifies as
   directives (pragmas, print, search, locate, GdumpWhy3). These
   don't advance uuid, so the session state is unchanged — the
   command is a pure query. Non-directive sentences are refused
   rather than silently advancing state. *)
(* Auto-append a period when [src] doesn't already end with one
   (ignoring trailing whitespace). Lets users type
   `:try print foo` or `:insert smt()` without the dot. *)
let ensure_terminator src =
  let n = ref (String.length src) in
  while !n > 0
        && (let c = src.[!n - 1] in c = ' ' || c = '\t'
            || c = '\n' || c = '\r')
  do decr n done;
  let trimmed = String.sub src 0 !n in
  if trimmed = "" then trimmed
  else if trimmed.[String.length trimmed - 1] = '.' then trimmed
  else trimmed ^ "."

(* Executable sentences of a document (drops [meta]). *)
let executables_of (doc : Document.t) =
  List.filter
    (fun (sn : Document.sentence) -> sn.parsed.cls <> `Meta)
    doc.sentences

let cmd_try st src =
  st.clear_result ();
  let src = ensure_terminator src in
  if not (Ec_llm_session.is_alive st.session) then
    emit st "session is dead; use :restart first"
  else match Ec_llm_session.parse_source st.session src with
    | Error e -> emit st "try: %s" (Error.to_string e)
    | Ok (sentences, _perr) ->
      let real = List.filter
          (fun (p : Ec_llm_session.parsed_sentence) -> p.cls <> `Meta)
          sentences
      in
      let non_directive =
        List.find_opt
          (fun (p : Ec_llm_session.parsed_sentence) -> p.cls <> `Directive)
          real
      in
      (match non_directive with
       | Some p ->
         emit st ":try refuses non-directive `%s` (class=%s); use :feed"
           p.kind
           (match p.cls with
            | `Executable -> "executable"
            | `Doc_comment -> "doc_comment"
            | `Meta -> "meta"
            | `Directive -> "directive")
       | None ->
         List.iter
           (fun (p : Ec_llm_session.parsed_sentence) ->
              ignore (exec_with_recovery st ~cls:`Directive
                        ~kind:p.kind ~src:p.src))
           real)

(* :exec-json <json> — submit a structured EC command via EXEC-JSON
   (addition 13). Useful for interactive testing and as the primary
   path MCP / LSP tools will use once Phases 5/6 land. *)
let cmd_exec_json st json_payload =
  st.clear_result ();
  st.goal_cursor <- 0;
  let json_payload = String.trim json_payload in
  if json_payload = "" then emit st ":exec-json needs a JSON payload"
  else if not (Ec_llm_session.is_alive st.session) then
    emit st "session is dead; :restart before :exec-json"
  else
    let corr = Correlation.of_client "repl-exec-json" in
    match Ec_llm_session.exec_json st.session ~corr ~command_json:json_payload with
    | Ok ok ->
      emit st "[exec-json    uuid=%d]  %s"
        ok.replied_uuid
        (if ok.restarted then "[restarted]" else "");
      List.iter (fun n -> emit st "  NOTICE: %s" n) ok.notices;
      emit_result st ok.output;
      if ok.restarted then st.executed <- []
    | Error (Error.Session_restarted { reason }) ->
      emit st "session died (%s); respawning…" reason;
      respawn_session st
    | Error e ->
      emit st "exec-json: %s" (Error.to_string e)

let cmd_feed st src =
  st.clear_result ();
  let src = ensure_terminator src in
  if not (Ec_llm_session.is_alive st.session) then
    emit st "session is dead; use :restart first"
  else match Ec_llm_session.parse_source st.session src with
    | Error e -> emit st "feed: %s" (Error.to_string e)
    | Ok (sentences, _perr) ->
      let executables =
        List.filter
          (fun (p : Ec_llm_session.parsed_sentence) -> p.cls <> `Meta)
          sentences
      in
      if executables = [] then emit st "(nothing to feed)"
      else
        let rec go = function
          | [] -> ()
          | (p : Ec_llm_session.parsed_sentence) :: rest ->
            (match
               exec_with_recovery st ~cls:(cls_of p) ~kind:p.kind ~src:p.src
             with
             | `Ok -> go rest
             | `Respawned | `Err -> ())
        in
        go executables

(* Path from a "file://…" uri used by [Document]. *)
let path_of_uri uri =
  if String.length uri > 7 && String.sub uri 0 7 = "file://"
  then String.sub uri 7 (String.length uri - 7)
  else uri

let write_file path content =
  let oc = open_out path in
  output_string oc content;
  close_out oc

(* Replace the current buffer with [new_source], re-parse it, and
   invoke [on_doc] with the freshly-parsed Document.t. Internal
   helper shared by :insert / :edit / :delete. Does NOT touch the
   filesystem — the buffer-vs-disk split is intentional: callers
   mutate memory freely and use :save to persist.

   Truncation guard: EC's PARSE-JSON stops at the first parse
   error and silently omits every sentence past that point. If a
   buffer edit accidentally produces unparseable text anywhere —
   leaving fewer post-edit executables than sentences we've
   already fed — the TUI's source pane visually "disappears" the
   tail and :step reads "end of document" while :diff still looks
   right (because doc.source holds the full text either way). We
   detect that state here, roll the buffer back, and tell the user
   what happened instead of committing a silently-broken view.

   [min_expected_executables] is the smallest number of executable
   sentences the caller expects the new parse to yield. :insert
   expects `old + inserted`; :edit expects `>= old`; :delete
   expects `old - 1`. When the reparse returns fewer, we warn.

   The reparse itself happens in [Edit_ops] now; this helper just
   assigns the new doc into state and runs the truncation check. *)
let commit_buffer st ~new_doc ~min_expected_executables ~on_doc =
  let new_exec_count = List.length (executables_of new_doc) in
  if new_exec_count < min_expected_executables then
    emit st "WARNING: reparse yielded only %d executable \
             sentences (expected ≥ %d). EC's parser stopped \
             early — display may be shorter than reality. \
             Buffer IS updated; :save still writes the full \
             content, :reload after save for a fresh parse."
      new_exec_count min_expected_executables;
  st.doc <- Some new_doc;
  on_doc new_doc

(* The sentence at the cursor — i.e. the one that would execute on
   the next :step. Returns [None] when the cursor has advanced past
   every executable sentence. *)
let cursor_sentence st =
  match st.doc with
  | None -> None
  | Some doc ->
    let executables = executables_of doc in
    List.nth_opt executables (List.length st.executed)

(* :insert — splice content in front of the cursor sentence (or at
   end-of-buffer when the cursor is past the last sentence),
   execute the spliced source, and advance st.executed across it.
   Buffer-only; the disk file is untouched until :save. *)
let cmd_insert st src =
  st.clear_result ();
  st.goal_cursor <- 0;
  let src = ensure_terminator (String.trim src) in
  if src = "" then emit st ":insert needs a source"
  else match st.doc with
    | None -> emit st "no document loaded; :insert requires a loaded file"
    | Some doc ->
      let executed_count = List.length st.executed in
      if not (Ec_llm_session.is_alive st.session) then
        emit st "session is dead; :restart before :insert"
      else match Ec_llm_session.parse_source st.session src with
        | Error e -> emit st "insert parse: %s" (Error.to_string e)
        | Ok (parsed, _perr) ->
          let real = List.filter
              (fun (p : Ec_llm_session.parsed_sentence) -> p.cls <> `Meta)
              parsed
          in
          if real = [] then emit st ":insert has no executable sentences"
          else begin
            let ran_all = ref true in
            let rec go = function
              | [] -> ()
              | (p : Ec_llm_session.parsed_sentence) :: rest ->
                (match exec_with_recovery st ~cls:(cls_of p)
                         ~kind:p.kind ~src:p.src with
                 | `Ok -> go rest
                 | `Respawned | `Err -> ran_all := false)
            in
            go real;
            if not !ran_all then
              emit st ":insert exec failed; buffer unchanged"
            else
              match
                Edit_ops.insert_before ~session:st.session ~doc
                  ~before_executable_index:executed_count ~content:src
              with
              | Error e -> emit st "insert reparse: %s" (Error.to_string e)
              | Ok new_doc ->
                let min_expected =
                  List.length (executables_of doc) + List.length real
                in
                commit_buffer st ~new_doc
                  ~min_expected_executables:min_expected
                  ~on_doc:(fun new_doc ->
                    let new_executables = executables_of new_doc in
                    let new_cursor = executed_count + List.length real in
                    let prefix =
                      List.filteri (fun i _ -> i < new_cursor)
                        new_executables
                    in
                    st.executed <- List.rev prefix;
                    emit st "inserted %d sentence(s); cursor=%d/%d \
                             (buffer modified, :save to persist)"
                      (List.length real) new_cursor
                      (List.length new_executables))
          end

(* :delete — remove the sentence AT the cursor (i.e. the next
   one to execute). The session state is unchanged, because the
   deleted sentence has not yet been fed through [exec]. The cursor
   naturally points to the following sentence after the shift.
   Buffer-only; :save to persist. *)
let cmd_delete st =
  st.clear_result ();
  st.goal_cursor <- 0;
  match cursor_sentence st with
  | None -> emit st "cursor past end; nothing to delete"
  | Some (target : Document.sentence) ->
    let doc = Option.get st.doc in
    match Edit_ops.delete ~session:st.session ~doc ~target with
    | Error e -> emit st "delete reparse: %s" (Error.to_string e)
    | Ok new_doc ->
      let min_expected = List.length (executables_of doc) - 1 in
      commit_buffer st ~new_doc
        ~min_expected_executables:min_expected
        ~on_doc:(fun new_doc ->
          let new_executables = executables_of new_doc in
          emit st "deleted %s at cursor %d; now %d/%d \
                   (buffer modified, :save to persist)"
            target.parsed.kind
            (List.length st.executed + 1)
            (List.length st.executed)
            (List.length new_executables))

(* :edit <src> — replace the sentence AT the cursor with [src].
   Session state is unchanged (the cursor sentence hadn't been
   executed yet). The edited content will be fed by the next :step.
   Buffer-only. *)
let cmd_edit st src =
  st.clear_result ();
  st.goal_cursor <- 0;
  let src = ensure_terminator src in
  if src = "" then emit st ":edit needs a source"
  else match cursor_sentence st with
    | None -> emit st "cursor past end; nothing to edit"
    | Some (target : Document.sentence) ->
      let doc = Option.get st.doc in
      match
        Edit_ops.replace ~session:st.session ~doc ~target ~content:src
      with
      | Error e -> emit st "edit reparse: %s" (Error.to_string e)
      | Ok new_doc ->
        let min_expected = List.length (executables_of doc) - 1 in
        commit_buffer st ~new_doc
          ~min_expected_executables:min_expected
          ~on_doc:(fun new_doc ->
            let new_executables = executables_of new_doc in
            emit st "edited %s at cursor %d; now %d/%d \
                     (buffer modified, :save to persist — :step to re-run)"
              target.parsed.kind
              (List.length st.executed + 1)
              (List.length st.executed)
              (List.length new_executables))

(* :save — write the in-memory buffer to disk and update the
   baseline against which :diff compares. *)
let cmd_save st =
  match st.doc with
  | None -> emit st "no document loaded"
  | Some doc ->
    if doc.source = st.disk_source then emit st "no changes to save"
    else
      let path = path_of_uri doc.uri in
      try
        write_file path doc.source;
        st.disk_source <- doc.source;
        emit st "saved %s (%d bytes)" path (String.length doc.source)
      with Sys_error msg -> emit st "save: %s" msg

(* Compact line-level diff between the in-memory buffer and the
   last-persisted content. Finds the longest common prefix/suffix
   of the two line lists and prints:
     -<removed>   (disk-only lines in the middle)
     +<added>     (buffer-only lines in the middle)
   No LCS alignment — good enough for quick visual review of
   pending :insert/:edit/:delete edits. *)
let cmd_diff st =
  match st.doc with
  | None -> emit st "no document loaded"
  | Some doc ->
    if doc.source = st.disk_source then
      emit st "no changes (buffer == disk)"
    else begin
      let a = String.split_on_char '\n' st.disk_source in
      let b = String.split_on_char '\n' doc.source in
      let rec common_prefix acc = function
        | x :: xs, y :: ys when x = y -> common_prefix (x :: acc) (xs, ys)
        | rest -> List.rev acc, rest
      in
      let prefix, (a_rest, b_rest) = common_prefix [] (a, b) in
      let ar, br = List.rev a_rest, List.rev b_rest in
      let suffix, (a_mid_r, b_mid_r) = common_prefix [] (ar, br) in
      let a_mid = List.rev a_mid_r in
      let b_mid = List.rev b_mid_r in
      let pre_ctx =
        let n = List.length prefix in
        let start = max 0 (n - 3) in
        List.filteri (fun i _ -> i >= start) prefix
      in
      let post_ctx = List.filteri (fun i _ -> i < 3) suffix in
      emit st "--- %s (on disk, %d bytes)"
        (path_of_uri doc.uri) (String.length st.disk_source);
      emit st "+++ buffer (%d bytes)" (String.length doc.source);
      List.iter (fun l -> st.out (" " ^ l)) pre_ctx;
      List.iter (fun l -> st.out ("-" ^ l)) a_mid;
      List.iter (fun l -> st.out ("+" ^ l)) b_mid;
      List.iter (fun l -> st.out (" " ^ l)) post_ctx
    end

let cmd_load st path =
  let content =
    try read_file path
    with Sys_error msg -> emit st "load: %s" msg; ""
  in
  if content = "" && not (Sys.file_exists path) then ()
  else match
    Document.parse st.session
      ~uri:("file://" ^ path)
      ~version:0
      ~source:content
  with
  | Error e -> emit st "load: %s" (Error.to_string e)
  | Ok d ->
    st.doc <- Some d;
    st.executed <- [];
    st.disk_source <- content;
    emit st "loaded %s: %d sentences" path (List.length d.sentences)

let cmd_reload st =
  st.clear_result ();
  st.goal_cursor <- 0;
  match st.doc with
  | None -> emit st "no document loaded"
  | Some old_doc ->
    let path = path_of_uri old_doc.uri in
    let content =
      try read_file path with Sys_error msg ->
        emit st "reload read: %s" msg; old_doc.source
    in
    st.disk_source <- content;
    (match
       Document.parse st.session ~uri:old_doc.uri
         ~version:(old_doc.version + 1)
         ~source:content
     with
     | Error e -> emit st "reload: %s" (Error.to_string e)
     | Ok new_doc ->
       let diff = Document.diff ~old:old_doc ~new_:new_doc in
       let prefix_len = List.length diff.unchanged_prefix in
       let cursor = List.length st.executed in
       emit st "diff: unchanged_prefix=%d removed=%d added=%d"
         prefix_len
         (List.length diff.removed) (List.length diff.added);
       if cursor > prefix_len && prefix_len > 0 then begin
         let last_good = List.nth diff.unchanged_prefix (prefix_len - 1) in
         (match Ec_llm_session.revert_to st.session last_good.id with
          | Ok () ->
            let drop = cursor - prefix_len in
            let rec drop_head k xs =
              if k <= 0 then xs
              else match xs with [] -> [] | _ :: t -> drop_head (k - 1) t
            in
            st.executed <- drop_head drop st.executed;
            emit st "rewound to uuid after sentence %d" prefix_len
          | Error e ->
            emit st "reload revert failed: %s" (Error.to_string e))
       end
       else if cursor > prefix_len && prefix_len = 0 then
         emit st "whole document changed; use :restart then :step";
       st.doc <- Some new_doc)

let cmd_restart st =
  st.clear_result ();
  st.goal_cursor <- 0;
  if not (Ec_llm_session.is_alive st.session) then begin
    respawn_session st;
    emit st "session respawned (fresh subprocess)"
  end
  else
    match
      Ec_llm_session.exec st.session
        ~corr:(Correlation.of_client "repl-restart")
        ~sentence_class:`Executable ~source:"pragma restart."
    with
    | Ok _ ->
      st.executed <- [];
      emit st "session restarted"
    | Error _ ->
      respawn_session st;
      emit st "session respawned (fresh subprocess)"

let help_lines = [
  "commands:";
  "  :load PATH          load and split an EC file";
  "  :reload             re-parse file, diff, rewind to common prefix";
  "  :step [N]           exec next N sentences (default 1)";
  "  n                   alias for :step 1";
  "  :back [N]           revert N executed sentences (default 1)";
  "  b                   alias for :back 1";
  "  :goals              focused subgoal (with Goal i/N indicator)";
  "  :goals json         raw GOALS-JSON payload";
  "  :goals plain        EC's own pretty-print (focused subgoal only)";
  "  :next-goal          cycle goal cursor forward";
  "  :prev-goal          cycle goal cursor backward";
  "  :feed <src>         execute an ad-hoc EC sentence";
  "  :try <src>          read-only one-shot: directives only \
                          (print / search / locate / pragma)";
  "  :exec-json <json>   submit a structured EC command via \
                          EXEC-JSON (addition 13)";
  "  :insert <src>       splice <src> in front of the cursor line, \
                          exec it, advance cursor (buffer-only)";
  "  :edit <src>          replace the cursor line with <src> \
                          (buffer-only; :step to re-exec)";
  "  :delete              remove the cursor line (buffer-only)";
  "  :save                write the buffer to disk";
  "  :diff                buffer-vs-disk diff of pending edits";
  "  :pos                print cursor/total/sid";
  "  :restart            issue pragma restart.";
  "  :help               this help";
  "  :quit / :q          exit";
]

let help st = List.iter st.out help_lines

(* --- Dispatch ------------------------------------------------------ *)

exception Quit

let trim = String.trim

let parse_int_arg rest default =
  let rest = trim rest in
  if rest = "" then default
  else try int_of_string rest with _ -> default

let dispatch st line =
  let line = trim line in
  if line = "" then ()
  else match line with
    | "n" -> cmd_step st 1
    | "b" -> cmd_back st 1
    | _ when String.length line >= 1 && line.[0] = ':' ->
      let rest = String.sub line 1 (String.length line - 1) in
      let (head, tail) =
        match String.index_opt rest ' ' with
        | None -> (rest, "")
        | Some i ->
          (String.sub rest 0 i,
           String.sub rest (i + 1) (String.length rest - i - 1))
      in
      (match head with
       | "load"    -> cmd_load st (trim tail)
       | "reload"  -> cmd_reload st
       | "step"    -> cmd_step st (parse_int_arg tail 1)
       | "back"    -> cmd_back st (parse_int_arg tail 1)
       | "goals"   ->
         let mode : goals_mode = match trim tail with
           | "json" -> `Json
           | "plain" -> `Plain
           | _ -> `Focused
         in
         cmd_goals ~mode st
       | "next-goal" -> cmd_next_goal st
       | "prev-goal" -> cmd_prev_goal st
       | "feed"    ->
         if tail = "" then emit st ":feed needs a source"
         else cmd_feed st tail
       | "try"     ->
         if tail = "" then emit st ":try needs a source"
         else cmd_try st tail
       | "exec-json" ->
         if tail = "" then emit st ":exec-json needs a JSON payload"
         else cmd_exec_json st tail
       | "insert"  ->
         if tail = "" then emit st ":insert needs a source"
         else cmd_insert st tail
       | "edit"    ->
         if tail = "" then emit st ":edit needs a source"
         else cmd_edit st tail
       | "delete"  -> cmd_delete st
       | "save"    -> cmd_save st
       | "diff"    -> cmd_diff st
       | "pos"     -> cmd_pos st
       | "restart" -> cmd_restart st
       | "help" | "h" -> help st
       | "quit" | "q" -> raise Quit
       | other -> emit st "unknown command :%s (see :help)" other)
    | _ ->
      (* Anything else is a raw EC sentence. *)
      cmd_feed st line
