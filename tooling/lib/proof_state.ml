type t = {
  mutable session : Ec_llm_session.t;
  mutable current_uri : string option;
  mutable cached_source : string;
  mutable cached_sentences : Ec_llm_session.parsed_sentence array;
  (* Highest-executed sentence index in [cached_sentences], or -1
     if nothing executed. Tracked directly — NOT derived by looking
     up session.executed_top in cached_sentences, because
     [Sentence_id.of_source] is a content hash and two sentences
     with identical source (`sp 1 1.` repeated, `unroll {1} 1.`
     repeated, etc.) collide on the same sid. The lookup would
     return the FIRST match instead of the actually-executed
     position — the locked region would visibly retract on every
     step past a duplicate. *)
  mutable current_index : int;
  primary_label : string;
  (* Working directory for the EC subprocess. UPSTREAM § 14′:
     per-project sessions need their own CWD so EC's
     [easycrypt.project] upward walk picks up the project's load
     paths. [None] = inherit daemon's CWD (the legacy single-
     session behavior). Cached here so [restart] / [ensure_doc]
     respawn into the same dir. *)
  cwd : string option;
  (* Serializes all access to the primary session. The LSP server
     forks each request as a fiber, so step/back/goals/exec/revert
     can race on the same session's stdin/stdout — same class of
     bug as the debouncer's overlapping process calls. *)
  mutex : Eio.Mutex.t;
}

let spawn_session ~cwd ~sw ~label =
  match cwd with
  | None -> Ec_llm_session.start ~sw ~label
  | Some d -> Ec_llm_session.start_in_dir ~cwd:d ~sw ~label

let create ~cwd ~sw ~primary_label =
  { session = spawn_session ~cwd ~sw ~label:primary_label;
    current_uri = None;
    cached_source = "";
    cached_sentences = [||];
    current_index = -1;
    primary_label;
    cwd;
    mutex = Eio.Mutex.create ();
  }

let with_lock t f =
  Eio.Mutex.use_rw ~protect:false t.mutex f

let close t =
  with_lock t (fun () -> Ec_llm_session.close t.session)

let restart t ~sw =
  with_lock t (fun () ->
    Ec_llm_session.close t.session;
    t.session <- spawn_session ~cwd:t.cwd ~sw ~label:t.primary_label;
    t.current_uri <- None;
    t.cached_source <- "";
    t.cached_sentences <- [||];
    t.current_index <- -1)

let parse_into_cache t ~source =
  match Ec_llm_session.parse_source t.session source with
  | Ok ss ->
    t.cached_sentences <- Array.of_list ss;
    t.cached_source <- source;
    Ok ()
  | Error e -> Error e

let ensure_doc t ~sw ~uri ~source =
  with_lock t (fun () ->
    let switching =
      match t.current_uri with
      | Some u -> u <> uri
      | None -> false
    in
    if switching then begin
      Ec_llm_session.close t.session;
      t.session <- spawn_session ~cwd:t.cwd ~sw ~label:t.primary_label;
      t.current_uri <- None;
      t.cached_source <- "";
      t.cached_sentences <- [||];
      t.current_index <- -1
    end;
    t.current_uri <- Some uri;
    if t.cached_source = source then Ok ()
    else parse_into_cache t ~source)

let current_uri t = t.current_uri
let sentences t = t.cached_sentences

(* Returns the sid of the sentence at the current index, derived
   from the cache rather than the session — keeps callers using the
   position-stable index. *)
let current_sentence_id t =
  let i = t.current_index in
  if i < 0 || i >= Array.length t.cached_sentences then None
  else Some (Sentence_id.of_source t.cached_sentences.(i).src)

let current_index t = t.current_index

(* (line, character) are 0-based LSP; sentence start_line/end_line
   are 1-based EC. We compare on (line, col) tuples. Resolution rule
   (matches PG): if the cursor is *inside* sentence i (between its
   start and end inclusive), return i. If the cursor is in the
   inter-sentence whitespace BEFORE sentence i (after sentence i-1's
   end), return i-1 — exec-to-cursor on a blank line should not
   advance into the next sentence. If the cursor is before the first
   sentence, return -1. If it's after the last sentence, return the
   last index. *)
let sentence_index_at_position t ~line ~character =
  let l = line + 1 and c = character + 1 in
  let n = Array.length t.cached_sentences in
  if n = 0 then -1
  else
    let pos_le sl sc el ec =
      sl < el || (sl = el && sc <= ec)
    in
    let rec scan i =
      if i >= n then n - 1
      else
        let s = t.cached_sentences.(i) in
        if pos_le l c s.end_line s.end_col then begin
          (* cursor is at-or-before sentence i's end. Decide whether
             it's WITHIN i (after its start) or in the whitespace
             gap before i. *)
          if pos_le s.start_line s.start_col l c then i
          else if i = 0 then -1
          else i - 1
        end
        else scan (i + 1)
    in
    scan 0

let exec_one t ~corr ~sentence ~sentence_class =
  Ec_llm_session.exec t.session ~corr ~sentence_class
    ~source:sentence.Ec_llm_session.src

let class_of_parse = function
  | `Executable -> Some `Executable
  | `Doc_comment -> Some `Doc_comment
  | `Directive -> Some `Directive
  | `Meta -> None

let sid_at_index t i =
  if i < 0 || i >= Array.length t.cached_sentences then None
  else Some (Sentence_id.of_source t.cached_sentences.(i).src)

(* Walk forward from [start_idx] up to and including [target], exec'ing
   each non-Meta sentence and updating [t.current_index] after each
   success. Stops at first error and reports the index where we stopped
   (== last successful index). Caller must hold the lock.

   [on_step], when provided, is invoked after each successful sentence
   exec with the new [current_index] and its sentence id. Lets callers
   stream incremental progress (e.g. PG-style per-sentence stateChanged
   emits). The callback runs INSIDE the held lock — keep it short
   (no I/O that could block the lock); writing a notification to a
   separately-mutex'd output stream is fine. *)
let exec_walk_unlocked ?on_step t ~start_idx ~target =
  let rec loop i =
    if i > target then Ok t.current_index
    else
      let s = t.cached_sentences.(i) in
      match class_of_parse s.cls with
      | None -> loop (i + 1)
      | Some sentence_class ->
        let corr = Correlation.fresh () in
        (match exec_one t ~corr ~sentence:s ~sentence_class with
         | Ok _ ->
           t.current_index <- i;
           (match on_step with
            | None -> ()
            | Some f ->
              let sid = sid_at_index t i in
              f t.current_index sid);
           loop (i + 1)
         | Error e -> Error (t.current_index, e))
  in
  loop start_idx

let exec_to ?on_step t ~target_index =
  with_lock t (fun () ->
    let n = Array.length t.cached_sentences in
    let target = min target_index (n - 1) in
    let cur = t.current_index in
    if target < cur then Ok cur
    else exec_walk_unlocked ?on_step t ~start_idx:(cur + 1) ~target)

(* Internal revert that updates [t.current_index] to match the
   post-revert position. Caller holds the lock. *)
let revert_to_index_unlocked t ~target_index =
  let r =
    if target_index < 0 then
      Ec_llm_session.revert_to_uuid t.session ~target:0
    else
      let s = t.cached_sentences.(target_index) in
      let sid = Sentence_id.of_source s.src in
      Ec_llm_session.revert_to t.session sid
  in
  match r with
  | Error e -> Error e
  | Ok () ->
    t.current_index <- (if target_index < 0 then -1 else target_index);
    Ok ()

let revert_to t ~target_index =
  with_lock t (fun () ->
    let cur = t.current_index in
    if target_index >= cur then Ok ()
    else revert_to_index_unlocked t ~target_index)

let goals t = with_lock t (fun () -> Ec_llm_session.goals t.session)

(* Atomic single-sentence step. Skips Meta. *)
let step_one t =
  with_lock t (fun () ->
    let n = Array.length t.cached_sentences in
    let cur = t.current_index in
    (* Advance to the first non-Meta sentence past cur. *)
    let rec next_executable i =
      if i >= n then None
      else
        match class_of_parse t.cached_sentences.(i).cls with
        | None -> next_executable (i + 1)
        | Some _ -> Some i
    in
    match next_executable (cur + 1) with
    | None -> `At_end
    | Some target ->
      (match exec_walk_unlocked t ~start_idx:(cur + 1) ~target with
       | Ok new_idx ->
         `Advanced (new_idx, sid_at_index t new_idx)
       | Error (last_idx, e) ->
         `Failed (last_idx, sid_at_index t last_idx, e)))

(* Atomic single-sentence back. *)
let back_one t =
  with_lock t (fun () ->
    let cur = t.current_index in
    if cur < 0 then `At_start
    else
      let target = cur - 1 in
      match revert_to_index_unlocked t ~target_index:target with
      | Error e -> `Failed e
      | Ok () ->
        let new_idx = t.current_index in
        `Reverted (new_idx, sid_at_index t new_idx))

(* Atomic snapshot for handlers that need consistent state. *)
type snapshot = {
  current_index : int;
  current_sentence_id : Sentence_id.t option;
  sentence_count : int;
}

let snapshot_unlocked t =
  let cur = current_index t in
  let sid =
    if cur < 0 then None
    else Some (Sentence_id.of_source t.cached_sentences.(cur).src)
  in
  { current_index = cur;
    current_sentence_id = sid;
    sentence_count = Array.length t.cached_sentences;
  }

let snapshot t = with_lock t (fun () -> snapshot_unlocked t)

let cancel_in_flight t =
  (* Intentionally unlocked: the request whose execution we're
     trying to interrupt is holding the mutex right now. Reading
     [t.session] without the lock is safe — [restart] only
     replaces the field while holding the lock, and the worst
     case (signal lands on a session that just got replaced) is
     a no-op SIGINT to a dead subprocess. *)
  Ec_llm_session.send_sigint t.session

let with_session t f =
  with_lock t (fun () -> f t.session)

let reconcile t ~uri ~source =
  with_lock t (fun () ->
    match t.current_uri with
    | None -> Ok `Not_bound
    | Some u when u <> uri -> Ok `Not_bound
    | Some _ ->
      if t.cached_source = source then Ok `Unchanged
      else
        match Ec_llm_session.parse_source t.session source with
        | Error e -> Error e
        | Ok ss ->
          let new_arr = Array.of_list ss in
          let cur_idx = current_index t in
          (* Common-prefix length over the parsed sentence list. *)
          let common_prefix =
            let rec count i =
              if i >= Array.length t.cached_sentences ||
                 i >= Array.length new_arr then i
              else if t.cached_sentences.(i).Ec_llm_session.src
                    = new_arr.(i).Ec_llm_session.src
              then count (i + 1)
              else i
            in
            count 0
          in
          (* New highest-executable index = min of the previous
             current_index and (common_prefix - 1). If divergence is
             past current_index, no retraction needed. *)
          let new_target = min cur_idx (common_prefix - 1) in
          let needs_retract = new_target < cur_idx in
          if needs_retract then begin
            let r =
              if new_target < 0 then
                Ec_llm_session.revert_to_uuid t.session ~target:0
              else
                let s = new_arr.(new_target) in
                let sid = Sentence_id.of_source s.src in
                Ec_llm_session.revert_to t.session sid
            in
            t.cached_sentences <- new_arr;
            t.cached_source <- source;
            (match r with
             | Error e -> Error e
             | Ok () ->
               t.current_index <-
                 (if new_target < 0 then -1 else new_target);
               Ok (`Reconciled (snapshot_unlocked t)))
          end
          else begin
            t.cached_sentences <- new_arr;
            t.cached_source <- source;
            Ok `Unchanged
          end)
