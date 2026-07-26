(** End-to-end smokes for [Proof_speculation].

    Covers:
    - Pure source builders (no session).
    - sort_suggest_rows ordering.
    - Cumulative-handle session: begin / try_ / discard, multi-try
      rollback discipline, commit drop, captured_uuid.
    - try_tactic one-shot sugar.
    - query (read-only directive dispatch + notices capture).
    - suggest_closers on a closable goal: early stop + on_progress
      callback ordering (decision 1: invoked AFTER rollback, so the
      session's current_uuid at callback time equals the capture uuid).
    - preview_lemma error-path on a non-resolving qname.

    Skipped without an [ec llm] binary on PATH or [EC_LLM_BIN] set. *)

open Ecd_core
open Eio.Std

let binary_path () =
  match Sys.getenv_opt "EC_LLM_BIN" with
  | Some p -> Some p
  | None ->
    let candidate = Filename.concat (Sys.getcwd ()) "_build/default/src/ec.exe" in
    if Sys.file_exists candidate then Some candidate
    else
      let ic = Unix.open_process_in "command -v easycrypt 2>/dev/null" in
      let line = try Some (input_line ic) with End_of_file -> None in
      let _ = Unix.close_process_in ic in
      line

let pass = ref 0
let fail = ref 0
let check label cond detail =
  if cond then begin incr pass; Printf.printf "  ok  %s\n%!" label end
  else begin incr fail; Printf.printf "  FAIL %s — %s\n%!" label detail end

(* --- Pure source builders ------------------------------------------ *)

let test_source_builders () =
  Printf.printf "== source builders ==\n%!";
  let h : Goal_view.hypothesis =
    { name = "H"; kind = Hyp; pp = "1 = 1" }
  in
  check "apply_hyp_source"
    (Proof_speculation.apply_hyp_source h = "apply H.")
    (Proof_speculation.apply_hyp_source h);

  check "move_cumulative_source empty"
    (Proof_speculation.move_cumulative_source [] = "move => .")
    (Proof_speculation.move_cumulative_source []);
  check "move_cumulative_source one"
    (Proof_speculation.move_cumulative_source ["x"] = "move => x.")
    (Proof_speculation.move_cumulative_source ["x"]);
  check "move_cumulative_source three"
    (Proof_speculation.move_cumulative_source ["x"; "H"; "?"]
     = "move => x H ?.")
    (Proof_speculation.move_cumulative_source ["x"; "H"; "?"]);

  check "rewrite_cumulative_source"
    (Proof_speculation.rewrite_cumulative_source ["H"; "-H'"; "/foo"]
     = "rewrite H -H' /foo.")
    (Proof_speculation.rewrite_cumulative_source ["H"; "-H'"; "/foo"]);

  check "verb_keyword apply"
    (Proof_speculation.verb_keyword `Apply = "apply") "";
  check "verb_keyword rewrite"
    (Proof_speculation.verb_keyword `Rewrite = "rewrite") "";

  let hit : Search_result.hit =
    { qname = "Int.addzC"; kind = "lemma"; short_name = "addzC"; signature = "" }
  in
  check "lemma_picker_source apply"
    (Proof_speculation.lemma_picker_source ~verb:`Apply hit
     = "apply Int.addzC.")
    (Proof_speculation.lemma_picker_source ~verb:`Apply hit);
  check "lemma_picker_source rewrite"
    (Proof_speculation.lemma_picker_source ~verb:`Rewrite hit
     = "rewrite Int.addzC.")
    (Proof_speculation.lemma_picker_source ~verb:`Rewrite hit)

(* --- Tactic catalog ------------------------------------------------ *)

let test_tactic_catalog () =
  Printf.printf "\n== tactic catalog ==\n%!";
  let cat = Proof_speculation.tactic_catalog in
  check "catalog has 6 entries"
    (List.length cat = 6)
    (Printf.sprintf "got %d" (List.length cat));
  let labels = List.map Proof_speculation.tactic_label cat in
  check "all labels nonempty"
    (List.for_all (fun s -> String.length s > 0) labels) ""

(* --- sort_suggest_rows --------------------------------------------- *)

let test_sort_suggest_rows () =
  Printf.printf "\n== sort_suggest_rows ==\n%!";
  let mk label outcome =
    { Proof_speculation.src = label ^ "."; label; outcome }
  in
  let input = [
    mk "trivial"     (Suggest_open 2);
    mk "by done"     (Suggest_err "boom");
    mk "reflexivity" Suggest_closes;
    mk "smt"         Suggest_closes;
    mk "assumption"  (Suggest_open 1);
  ] in
  let sorted = Proof_speculation.sort_suggest_rows input in
  let labels = List.map (fun r -> r.Proof_speculation.label) sorted in
  check "closers first then open then err"
    (labels = ["reflexivity"; "smt"; "trivial"; "assumption"; "by done"])
    (String.concat "," labels)

(* --- Session-based tests ------------------------------------------- *)

let exec_executable s ~source =
  let corr = Correlation.of_client "feed" in
  match Ec_llm_session.exec s ~corr ~sentence_class:`Executable ~source with
  | Ok _ -> ()
  | Error e ->
    Printf.eprintf "feed failed (%s): %s\n%!" source (Error.to_string e);
    exit 1

let setup_session s =
  exec_executable s ~source:"require import AllCore.";
  exec_executable s ~source:"lemma _spec_smoke : 1 = 1.";
  exec_executable s ~source:"proof."

let test_begin_try_discard s =
  Printf.printf "\n== begin/try/discard ==\n%!";
  let pre = Ec_llm_session.current_uuid s in
  let session = Proof_speculation.begin_session s in
  check "captured_uuid"
    (Proof_speculation.captured_uuid session = pre)
    (Printf.sprintf "captured %d vs pre %d"
       (Proof_speculation.captured_uuid session) pre);

  (match Proof_speculation.try_ session ~source:"reflexivity." with
   | Trial_ok { goals; body = _ } ->
     check "try_ Trial_ok" true "";
     check "try_ goals=Some" (goals <> None) "no goals returned";
     check "try_ advanced uuid"
       (Ec_llm_session.current_uuid s > pre)
       (Printf.sprintf "uuid %d not > %d"
          (Ec_llm_session.current_uuid s) pre)
   | Trial_err e -> check "try_ Trial_ok" false e);

  (match Proof_speculation.discard session with
   | Ok () ->
     check "discard restored uuid"
       (Ec_llm_session.current_uuid s = pre)
       (Printf.sprintf "uuid %d != pre %d"
          (Ec_llm_session.current_uuid s) pre)
   | Error e -> check "discard ok" false (Error.to_string e))

let test_multi_try s =
  Printf.printf "\n== multi-try (rollback between each) ==\n%!";
  let pre = Ec_llm_session.current_uuid s in
  let session = Proof_speculation.begin_session s in

  (* Each try rolls back to capture, then execs. *)
  (match Proof_speculation.try_ session ~source:"trivial." with
   | Trial_ok _ -> check "try1 ok" true ""
   | Trial_err e -> check "try1 ok" false e);
  let after_try1 = Ec_llm_session.current_uuid s in
  check "try1 advanced uuid"
    (after_try1 > pre)
    (Printf.sprintf "%d !> %d" after_try1 pre);

  (match Proof_speculation.try_ session ~source:"reflexivity." with
   | Trial_ok _ -> check "try2 ok" true ""
   | Trial_err e -> check "try2 ok" false e);
  let after_try2 = Ec_llm_session.current_uuid s in
  check "try2 advanced from capture (not from try1)"
    (after_try2 = after_try1)
    (Printf.sprintf "expected %d (try1 uuid since each try captures only +1), got %d"
       after_try1 after_try2);

  (match Proof_speculation.discard session with
   | Ok () ->
     check "discard back to pre"
       (Ec_llm_session.current_uuid s = pre)
       (Printf.sprintf "got %d expected %d"
          (Ec_llm_session.current_uuid s) pre)
   | Error e -> check "discard ok" false (Error.to_string e))

let test_commit s =
  Printf.printf "\n== commit (drops rollback right) ==\n%!";
  let pre = Ec_llm_session.current_uuid s in
  let session = Proof_speculation.begin_session s in
  (match Proof_speculation.try_ session ~source:"trivial." with
   | Trial_ok _ ->
     let post_try = Ec_llm_session.current_uuid s in
     check "post-try uuid > pre"
       (post_try > pre)
       (Printf.sprintf "%d !> %d" post_try pre);
     (match Proof_speculation.commit session with
      | Ok () ->
        check "post-commit uuid unchanged"
          (Ec_llm_session.current_uuid s = post_try)
          (Printf.sprintf "got %d expected %d"
             (Ec_llm_session.current_uuid s) post_try)
      | Error e -> check "commit ok" false (Error.to_string e));
     (* Caller still owns the cleanup — revert manually so the next
        test starts at a known pre-state. *)
     (match Ec_llm_session.revert_to_uuid s ~target:pre with
      | Ok () -> ()
      | Error e ->
        Printf.eprintf "manual revert failed: %s\n%!" (Error.to_string e);
        exit 1)
   | Trial_err e -> check "trivial try ok" false e)

let test_try_tactic s =
  Printf.printf "\n== try_tactic one-shot sugar ==\n%!";
  let pre = Ec_llm_session.current_uuid s in
  (match Proof_speculation.try_tactic s ~source:"reflexivity." with
   | Trial_ok _ -> check "try_tactic Trial_ok" true ""
   | Trial_err e -> check "try_tactic Trial_ok" false e);
  check "try_tactic returns session to pre"
    (Ec_llm_session.current_uuid s = pre)
    (Printf.sprintf "got %d expected %d"
       (Ec_llm_session.current_uuid s) pre)

let test_query s =
  Printf.printf "\n== query (read-only directive) ==\n%!";
  let pre = Ec_llm_session.current_uuid s in
  (match Proof_speculation.query s ~source:"print Int.addzC." with
   | Ok { body; notices = _ } ->
     check "query body nonempty" (String.length body > 0) "empty body";
     check "query did not advance uuid"
       (Ec_llm_session.current_uuid s = pre)
       (Printf.sprintf "uuid %d != pre %d"
          (Ec_llm_session.current_uuid s) pre)
   | Error e -> check "query ok" false (Error.to_string e))

let test_suggest_closers s =
  Printf.printf "\n== suggest_closers (early stop + callback ordering) ==\n%!";
  let pre = Ec_llm_session.current_uuid s in
  (* Track the interleaved trace of both callbacks plus the session
     uuid observed at each call. Both hooks fire at rollback-stable
     boundaries — uuid should equal [pre] every time. *)
  let trace = ref [] in
  let push e = trace := e :: !trace in
  let before_candidate ~label ~remaining =
    push (`Before (label, remaining, Ec_llm_session.current_uuid s))
  in
  let on_progress (row : Proof_speculation.suggest_row) ~remaining =
    push (`After (row, remaining, Ec_llm_session.current_uuid s))
  in
  (match
     Proof_speculation.suggest_closers s
       ~before_candidate ~on_progress ()
   with
   | Error e -> check "suggest_closers ok" false (Error.to_string e)
   | Ok rows ->
     let events = List.rev !trace in
     check "non-empty rows"
       (List.length rows > 0)
       (Printf.sprintf "got %d rows" (List.length rows));
     check "early stop on first closer"
       (let last = List.nth rows (List.length rows - 1) in
        last.Proof_speculation.outcome = Suggest_closes)
       (Printf.sprintf "%d rows, last is not Suggest_closes"
          (List.length rows));
     check "session restored to pre after sweep"
       (Ec_llm_session.current_uuid s = pre)
       (Printf.sprintf "uuid %d != pre %d"
          (Ec_llm_session.current_uuid s) pre);

     let uuids_seen =
       List.map (function
           | `Before (_, _, u) -> u
           | `After (_, _, u) -> u)
         events
     in
     check "all callbacks fire at base uuid (rollback-stable)"
       (List.for_all ((=) pre) uuids_seen)
       (Printf.sprintf "uuids: %s; expected all %d"
          (String.concat "," (List.map string_of_int uuids_seen))
          pre);

     (* Every row should be wrapped by exactly one Before / After
        pair. The trace alternates [Before; After; Before; After; …]
        with one pair per emitted row. *)
     let n_rows = List.length rows in
     let n_before =
       List.fold_left
         (fun n e -> match e with `Before _ -> n + 1 | _ -> n)
         0 events
     in
     let n_after =
       List.fold_left
         (fun n e -> match e with `After _ -> n + 1 | _ -> n)
         0 events
     in
     check "before_candidate fires once per row"
       (n_before = n_rows)
       (Printf.sprintf "before=%d rows=%d" n_before n_rows);
     check "on_progress fires once per row"
       (n_after = n_rows)
       (Printf.sprintf "after=%d rows=%d" n_after n_rows);

     (* Strict alternation: pairs[i] = (Before, After) for row i. *)
     let rec check_alternation i = function
       | [] -> i = n_rows
       | `Before _ :: `After _ :: rest -> check_alternation (i + 1) rest
       | _ -> false
     in
     check "before/after strictly interleaved per row"
       (check_alternation 0 events) "non-alternating trace";

     (* Remaining counters: before_candidate sees [total..total-n_rows+1].
        on_progress sees [total-1..total-n_rows]. (Counters reflect
        the full default candidate list, not just the rows that
        eventually run — early stop trims the trace.) *)
     let total = List.length Proof_speculation.default_closer_candidates in
     let before_remainings =
       List.filter_map
         (function `Before (_, r, _) -> Some r | _ -> None)
         events
     in
     let after_remainings =
       List.filter_map
         (function `After (_, r, _) -> Some r | _ -> None)
         events
     in
     let expected_before =
       List.init n_rows (fun i -> total - i)
     in
     let expected_after =
       List.init n_rows (fun i -> total - i - 1)
     in
     check "before remaining counts down from total"
       (before_remainings = expected_before)
       (Printf.sprintf "got [%s] expected [%s]"
          (String.concat ";" (List.map string_of_int before_remainings))
          (String.concat ";" (List.map string_of_int expected_before)));
     check "after remaining = before remaining - 1 per row"
       (after_remainings = expected_after)
       (Printf.sprintf "got [%s] expected [%s]"
          (String.concat ";" (List.map string_of_int after_remainings))
          (String.concat ";" (List.map string_of_int expected_after)));

     (* The label passed to before_candidate matches the label of the
        row reported by the next on_progress. *)
     let labels_match =
       let rec walk = function
         | [] -> true
         | `Before (lbl, _, _)
           :: `After ((row : Proof_speculation.suggest_row), _, _)
           :: rest ->
           lbl = row.label && walk rest
         | _ -> false
       in
       walk events
     in
     check "before label matches following row label" labels_match
       "label mismatch in before/after pair")

let test_preview_lemma_error_path s =
  Printf.printf "\n== preview_lemma error path (non-resolving qname) ==\n%!";
  let pre = Ec_llm_session.current_uuid s in
  let bad : Search_result.hit =
    { qname = "Nonexistent.lemma_does_not_exist"
    ; kind = "lemma"
    ; short_name = "lemma_does_not_exist"
    ; signature = ""
    }
  in
  (match Proof_speculation.preview_lemma s ~verb:`Apply bad with
   | Ok (Preview_err _, session) ->
     check "preview_lemma yields Preview_err on bad hit" true "";
     (match Proof_speculation.discard session with
      | Ok () ->
        check "discard restored uuid post error preview"
          (Ec_llm_session.current_uuid s = pre)
          (Printf.sprintf "uuid %d != pre %d"
             (Ec_llm_session.current_uuid s) pre)
      | Error e -> check "discard error preview ok" false (Error.to_string e))
   | Ok (Preview_ok _, _) ->
     check "preview_lemma should have errored on bad hit" false ""
   | Error e ->
     check "preview_lemma should not surface Error on bad hit" false
       (Error.to_string e))

(* Drive the session into a state with multiple subgoals (split a
   conjunction), focus on the first one, then assert that
   suggest_closers detects [reflexivity] as a CLOSER even though
   the unrelated second subgoal remains open. Pre-fix this returned
   [Suggest_open 1] (misleading) because the implementation looked
   only at total subgoal_count, not the count delta. *)
let test_suggest_closers_multi_subgoal s =
  Printf.printf
    "\n== suggest_closers (closer detection on multi-subgoal goal) ==\n%!";
  (* Close the previous proof (still open from earlier tests in this
     session) before declaring a new lemma. abort. drops the open
     proof without committing. *)
  exec_executable s ~source:"abort.";
  (* New lemma with a conjunction; split to get 2 subgoals. *)
  exec_executable s ~source:"lemma _spec_multi : 1 = 1 /\\ 2 = 2.";
  exec_executable s ~source:"proof.";
  exec_executable s ~source:"split.";

  (* Capture pre-sweep state for diagnostics. *)
  let pre_count =
    match Ec_llm_session.goals ~structured:true s with
    | Ok json ->
      (match Goal_view.of_string json with
       | Ok gv -> gv.subgoal_count
       | Error _ -> -1)
    | Error _ -> -1
  in
  check "pre-sweep has 2 subgoals after split"
    (pre_count = 2)
    (Printf.sprintf "got %d" pre_count);

  match Proof_speculation.suggest_closers s () with
  | Error e ->
    check "suggest_closers ok (multi-subgoal)" false (Error.to_string e)
  | Ok rows ->
    check "non-empty rows (multi-subgoal)"
      (List.length rows > 0)
      (Printf.sprintf "got %d rows" (List.length rows));
    (* reflexivity closes the focused [1 = 1] subgoal; one unrelated
       subgoal [2 = 2] remains. Should be Suggest_closes (delta < 0),
       NOT Suggest_open 1 (which the pre-fix code reported). *)
    let last = List.nth rows (List.length rows - 1) in
    check "last row is Suggest_closes (focused subgoal closed)"
      (last.Proof_speculation.outcome = Suggest_closes)
      (Printf.sprintf "got outcome=%s, label=%s"
         (match last.outcome with
          | Suggest_closes -> "Suggest_closes"
          | Suggest_open n -> Printf.sprintf "Suggest_open %d" n
          | Suggest_err msg -> Printf.sprintf "Suggest_err %S" msg)
         last.label);
    (* The closer should be reflexivity (cheapest candidate that
       closes 1 = 1). *)
    check "closer label is reflexivity"
      (last.label = "reflexivity")
      last.label;
    (* Session is restored to pre-sweep state (still 2 subgoals
       open after the speculative sweep rolls back). *)
    let post_count =
      match Ec_llm_session.goals ~structured:true s with
      | Ok json ->
        (match Goal_view.of_string json with
         | Ok gv -> gv.subgoal_count
         | Error _ -> -1)
      | Error _ -> -1
    in
    check "post-sweep state restored (still 2 subgoals)"
      (post_count = 2)
      (Printf.sprintf "got %d expected 2" post_count)

let test_session ~bin env =
  Printf.printf "\n== session ==\n%!";
  Switch.run @@ fun sw ->
  let process_mgr = Eio.Stdenv.process_mgr env in
  Ec_llm_session.configure ~process_mgr
    ~executable:bin
    ~extra_args:[ "-I"; Filename.concat (Sys.getcwd ()) "theories" ] ();
  let s = Ec_llm_session.start ~sw ~label:"proof-spec" in
  setup_session s;
  test_begin_try_discard s;
  test_multi_try s;
  test_commit s;
  test_try_tactic s;
  test_query s;
  test_suggest_closers s;
  test_preview_lemma_error_path s;
  test_suggest_closers_multi_subgoal s;
  Ec_llm_session.close s

(* --- Main ---------------------------------------------------------- *)

let () =
  test_source_builders ();
  test_tactic_catalog ();
  test_sort_suggest_rows ();
  (match binary_path () with
   | None ->
     Printf.printf
       "\n== session ==\n  skip: no ec llm binary found (set EC_LLM_BIN)\n%!"
   | Some bin ->
     Eio_main.run (fun env -> test_session ~bin env));
  Printf.printf "\n== summary ==\n";
  Printf.printf "  pass=%d  fail=%d\n%!" !pass !fail;
  exit (if !fail = 0 then 0 else 1)
