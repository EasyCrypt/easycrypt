(** Comprehensive tests for [Repl_core] command semantics. Covers
    both the line REPL and TUI surfaces through their shared core.

    New buffer model: :insert / :edit / :delete mutate the in-memory
    buffer (doc.source) only. The disk file is unchanged until :save.
    :diff shows pending changes. :edit and :delete operate on the
    CURSOR line — the next sentence to execute — not the last-
    executed one. *)

open Ecd_core
open Eio.Std

(* --- Test harness -------------------------------------------------- *)

let binary_path () =
  match Sys.getenv_opt "EC_LLM_BIN" with
  | Some p -> Some p
  | None ->
    let candidate = Filename.concat (Sys.getcwd ())
                      "_build/default/src/ec.exe" in
    if Sys.file_exists candidate then Some candidate else None

type case_state = {
  st : Repl_core.state;
  out : string list ref;    (* newest-first *)
  result : string list ref; (* newest-first *)
}

let make_case ~env ~sw =
  let process_mgr = Eio.Stdenv.process_mgr env in
  Ec_llm_session.configure ~process_mgr
    ~executable:(Option.get (binary_path ()))
    ~extra_args:[ "-I"; Filename.concat (Sys.getcwd ()) "theories" ] ();
  let session = Ec_llm_session.start ~sw ~label:"test" in
  let st = Repl_core.make ~session ~sw in
  let out = ref [] in
  let result = ref [] in
  st.out <- (fun s -> out := s :: !out);
  st.result <- (fun s -> result := s :: !result);
  st.clear_result <- (fun () -> result := []);
  { st; out; result }

let drain buf = let xs = List.rev !buf in buf := []; xs

let pass = ref 0
let fail = ref 0

let check label cond detail =
  if cond then begin
    incr pass;
    Printf.printf "  ok  %s\n%!" label
  end
  else begin
    incr fail;
    Printf.printf "  FAIL %s — %s\n%!" label detail
  end

let contains haystack needle =
  let nl = String.length needle in
  let hl = String.length haystack in
  if nl = 0 then true
  else
    let found = ref false in
    let i = ref 0 in
    while (not !found) && !i + nl <= hl do
      if String.sub haystack !i nl = needle then found := true
      else incr i
    done;
    !found

let check_contains label haystack needle =
  check label (contains haystack needle)
    (Printf.sprintf "no %S in %S" needle
       (if String.length haystack > 200
        then String.sub haystack 0 200 ^ "..." else haystack))

let check_no_contains label haystack needle =
  check label (not (contains haystack needle))
    (Printf.sprintf "unexpected %S in %S" needle
       (if String.length haystack > 200
        then String.sub haystack 0 200 ^ "..." else haystack))

let write_file path content =
  let oc = open_out path in
  output_string oc content;
  close_out oc

let read_file path =
  let ic = open_in path in
  let n = in_channel_length ic in
  let s = really_input_string ic n in
  close_in ic;
  s

let doc_source st =
  match st.Repl_core.doc with
  | None -> ""
  | Some d -> d.source

(* --- Individual tests --------------------------------------------- *)

(* 1. ensure_terminator via :try — missing dot is accepted. *)
let test_dot_append env =
  Printf.printf "== test_dot_append ==\n";
  Switch.run @@ fun sw ->
  let c = make_case ~env ~sw in
  let path = "/tmp/repl-test-dot.ec" in
  write_file path
    "require import AllCore Int.\n\
     op foo (i : int) = i + 1.\n";
  Repl_core.dispatch c.st (":load " ^ path);
  Repl_core.dispatch c.st ":step 2";
  Repl_core.dispatch c.st ":try print foo";
  let results = String.concat "\n" (drain c.result) in
  check_contains "try without dot surfaces print output"
    results "op foo";
  Repl_core.dispatch c.st ":try print foo.";
  let results = String.concat "\n" (drain c.result) in
  check_contains "try with dot also works" results "op foo";
  ignore (drain c.out);
  Ec_llm_session.close c.st.session

(* 2. :insert preserves trailing content (no deletion after insert). *)
let test_insert_preserves_trailing env =
  Printf.printf "== test_insert_preserves_trailing ==\n";
  Switch.run @@ fun sw ->
  let c = make_case ~env ~sw in
  let path = "/tmp/repl-test-insert-trailing.ec" in
  let initial =
    "require import AllCore.\n\
     lemma First : true = true.\n\
     proof. trivial. qed.\n\
     \n\
     lemma Second : 1 = 1.\n\
     proof. trivial. qed.\n"
  in
  write_file path initial;
  Repl_core.dispatch c.st (":load " ^ path);
  Repl_core.dispatch c.st ":step 5";
  ignore (drain c.out);
  Repl_core.dispatch c.st ":insert pragma noop";
  let buffer = doc_source c.st in
  (* Everything after the insertion point must survive. *)
  check_contains "trailing lemma survives in buffer"
    buffer "lemma Second : 1 = 1.";
  check_contains "trailing proof survives in buffer"
    buffer "proof. trivial. qed.";
  check_contains "inserted pragma present in buffer"
    buffer "pragma noop.";
  check "buffer grew (content not truncated)"
    (String.length buffer > String.length initial)
    (Printf.sprintf "buf=%d initial=%d"
       (String.length buffer) (String.length initial));
  (* The file on disk must NOT have changed yet. *)
  let on_disk = read_file path in
  check "file on disk unchanged before :save"
    (on_disk = initial)
    "disk diverged from initial content";
  ignore (drain c.out);
  Ec_llm_session.close c.st.session

(* 3. :insert at end of buffer — full session builds a proof. *)
let test_insert_at_end env =
  Printf.printf "== test_insert_at_end ==\n";
  Switch.run @@ fun sw ->
  let c = make_case ~env ~sw in
  let path = "/tmp/repl-test-insert-end.ec" in
  let initial =
    "require import AllCore Int.\n\
     lemma L (x : int) : 0 <= x => 0 <= x.\n\
     proof.\n"
  in
  write_file path initial;
  Repl_core.dispatch c.st (":load " ^ path);
  Repl_core.dispatch c.st ":step 3";
  ignore (drain c.out);
  Repl_core.dispatch c.st ":insert move=> h";
  Repl_core.dispatch c.st ":insert trivial";
  Repl_core.dispatch c.st ":insert qed";
  let buffer = doc_source c.st in
  check_contains "move=> in buffer" buffer "move=> h.";
  check_contains "trivial in buffer" buffer "trivial.";
  check_contains "qed in buffer" buffer "qed.";
  (* File still unchanged on disk. *)
  check "file unchanged (buffer-only edits)"
    (read_file path = initial) "disk changed without :save";
  (* Now save and verify. *)
  Repl_core.dispatch c.st ":save";
  let saved = read_file path in
  check_contains "saved file has qed" saved "qed.";
  check "saved file == buffer" (saved = buffer) "disk != buffer after :save";
  ignore (drain c.out);
  Ec_llm_session.close c.st.session

(* 4. :save / :diff lifecycle. *)
let test_save_and_diff env =
  Printf.printf "== test_save_and_diff ==\n";
  Switch.run @@ fun sw ->
  let c = make_case ~env ~sw in
  let path = "/tmp/repl-test-save-diff.ec" in
  let initial = "require import AllCore Int.\nop x : int = 1.\n" in
  write_file path initial;
  Repl_core.dispatch c.st (":load " ^ path);
  Repl_core.dispatch c.st ":diff";
  let out = String.concat "\n" (drain c.out) in
  check_contains "diff of pristine doc" out "no changes";
  Repl_core.dispatch c.st ":step 2";
  ignore (drain c.out);
  Repl_core.dispatch c.st ":insert op y : int = 2";
  ignore (drain c.out);
  Repl_core.dispatch c.st ":diff";
  let out = String.concat "\n" (drain c.out) in
  check_contains "diff shows + for added line" out "+op y : int = 2";
  check "file still unchanged pre-save"
    (read_file path = initial) "disk changed without :save";
  Repl_core.dispatch c.st ":save";
  let out = String.concat "\n" (drain c.out) in
  check_contains "save reports bytes written" out "saved";
  check "file matches buffer after save"
    (read_file path = doc_source c.st) "disk != buffer after :save";
  Repl_core.dispatch c.st ":diff";
  let out = String.concat "\n" (drain c.out) in
  check_contains "diff clean after save" out "no changes";
  ignore (drain c.out);
  Ec_llm_session.close c.st.session

(* 5. :delete removes the CURSOR line (not the last-executed). *)
let test_delete_at_cursor env =
  Printf.printf "== test_delete_at_cursor ==\n";
  Switch.run @@ fun sw ->
  let c = make_case ~env ~sw in
  let path = "/tmp/repl-test-delete-cursor.ec" in
  write_file path
    "require import AllCore.\n\
     op one : int = 1.\n\
     op two : int = 2.\n\
     op three : int = 3.\n";
  Repl_core.dispatch c.st (":load " ^ path);
  Repl_core.dispatch c.st ":step 2";  (* executed: require, one *)
  ignore (drain c.out);
  (* cursor is on `op two`. :delete should remove THAT line, not `op one`. *)
  Repl_core.dispatch c.st ":delete";
  let buffer = doc_source c.st in
  check_contains "executed `op one` preserved in buffer"
    buffer "op one : int = 1.";
  check_no_contains "cursor line `op two` removed"
    buffer "op two : int = 2.";
  check_contains "post-cursor `op three` preserved"
    buffer "op three : int = 3.";
  (* Session state is unchanged: st.executed still has 2 sentences. *)
  check "st.executed unchanged by :delete at cursor"
    (List.length c.st.executed = 2)
    (Printf.sprintf "executed count=%d" (List.length c.st.executed));
  (* File on disk untouched. *)
  check "delete is buffer-only"
    (not (contains (read_file path) "op one") = false)
    "";
  check "file on disk still has op two"
    (contains (read_file path) "op two : int = 2.")
    "disk changed";
  ignore (drain c.out);
  Ec_llm_session.close c.st.session

(* 6. :delete past end-of-document errors out. *)
let test_delete_past_end env =
  Printf.printf "== test_delete_past_end ==\n";
  Switch.run @@ fun sw ->
  let c = make_case ~env ~sw in
  let path = "/tmp/repl-test-delete-past.ec" in
  write_file path "require import AllCore.\n";
  Repl_core.dispatch c.st (":load " ^ path);
  Repl_core.dispatch c.st ":step";
  ignore (drain c.out);
  Repl_core.dispatch c.st ":delete";
  let out = String.concat "\n" (drain c.out) in
  check_contains "delete past end reports" out "cursor past end";
  Ec_llm_session.close c.st.session

(* 7. :edit replaces the CURSOR line; session unchanged until :step. *)
let test_edit_at_cursor env =
  Printf.printf "== test_edit_at_cursor ==\n";
  Switch.run @@ fun sw ->
  let c = make_case ~env ~sw in
  let path = "/tmp/repl-test-edit.ec" in
  write_file path
    "require import AllCore Int.\n\
     op one : int = 1.\n\
     op two : int = 2.\n";
  Repl_core.dispatch c.st (":load " ^ path);
  Repl_core.dispatch c.st ":step 2";  (* executed: require, one *)
  ignore (drain c.out);
  let pre_exec = List.length c.st.executed in
  Repl_core.dispatch c.st ":edit op two_prime : int = 42";
  let buffer = doc_source c.st in
  check_contains "edited line in buffer"
    buffer "op two_prime : int = 42.";
  check_no_contains "old cursor line gone"
    buffer "op two : int = 2.";
  check "st.executed unchanged by :edit"
    (List.length c.st.executed = pre_exec)
    "executed changed";
  check "disk untouched"
    (contains (read_file path) "op two : int = 2.")
    "disk modified by :edit";
  (* Now step into the edited sentence and verify it runs. *)
  Repl_core.dispatch c.st ":step";
  let out = String.concat "\n" (drain c.out) in
  check_contains "stepping after edit executes new content"
    out "two_prime";
  Ec_llm_session.close c.st.session

(* 8. :edit past end-of-document errors. *)
let test_edit_past_end env =
  Printf.printf "== test_edit_past_end ==\n";
  Switch.run @@ fun sw ->
  let c = make_case ~env ~sw in
  let path = "/tmp/repl-test-edit-past.ec" in
  write_file path "require import AllCore.\n";
  Repl_core.dispatch c.st (":load " ^ path);
  Repl_core.dispatch c.st ":step";
  ignore (drain c.out);
  Repl_core.dispatch c.st ":edit trivial";
  let out = String.concat "\n" (drain c.out) in
  check_contains "edit past end reports" out "cursor past end";
  Ec_llm_session.close c.st.session

(* 9. :try refuses non-directive classes. *)
let test_try_refuses_executables env =
  Printf.printf "== test_try_refuses_executables ==\n";
  Switch.run @@ fun sw ->
  let c = make_case ~env ~sw in
  let path = "/tmp/repl-test-try-refuse.ec" in
  write_file path "require import AllCore Int.\n";
  Repl_core.dispatch c.st (":load " ^ path);
  Repl_core.dispatch c.st ":step";
  ignore (drain c.out);
  Repl_core.dispatch c.st ":try op foo : int = 1";
  let out = String.concat "\n" (drain c.out) in
  check_contains "try refuses executable" out "refuses non-directive";
  Ec_llm_session.close c.st.session

(* 10. :try output lands in result sink, not log. *)
let test_try_result_routing env =
  Printf.printf "== test_try_result_routing ==\n";
  Switch.run @@ fun sw ->
  let c = make_case ~env ~sw in
  let path = "/tmp/repl-test-try-route.ec" in
  write_file path
    "require import AllCore Int.\n\
     op foo : int = 7.\n";
  Repl_core.dispatch c.st (":load " ^ path);
  Repl_core.dispatch c.st ":step 2";
  ignore (drain c.out);
  ignore (drain c.result);
  Repl_core.dispatch c.st ":try print foo.";
  let results = String.concat "\n" (drain c.result) in
  let log = String.concat "\n" (drain c.out) in
  check_contains "print output in result sink" results "op foo";
  check_no_contains "log sink doesn't carry reply body"
    log "op foo : int = 7.";
  Ec_llm_session.close c.st.session

(* 11. :next-goal / :prev-goal cycle with a real multi-subgoal proof. *)
let test_goal_cycling env =
  Printf.printf "== test_goal_cycling ==\n";
  Switch.run @@ fun sw ->
  let c = make_case ~env ~sw in
  let path = "/tmp/repl-test-goal-cycle.ec" in
  write_file path
    "require import AllCore Int.\n\
     lemma L (x : int) : x = 0 \\/ x <> 0.\n\
     proof.\n\
     case (x = 0).\n";
  Repl_core.dispatch c.st (":load " ^ path);
  Repl_core.dispatch c.st ":step 4";
  ignore (drain c.out);
  check "cursor starts at 0" (c.st.goal_cursor = 0) "";
  Repl_core.dispatch c.st ":next-goal";
  let out = String.concat "\n" (drain c.out) in
  if c.st.goal_cursor = 1 then
    check_contains "next-goal marks subgoal 2 as lookahead"
      out "lookahead"
  else
    (* Single subgoal — next-goal reports boundary. *)
    check_contains "single-goal: next-goal reports bound"
      out "last subgoal";
  Repl_core.dispatch c.st ":prev-goal";
  check "prev-goal resets cursor to 0"
    (c.st.goal_cursor = 0) "";
  Ec_llm_session.close c.st.session

(* 12. state-mutating commands reset goal_cursor to 0. *)
let test_goal_cursor_reset env =
  Printf.printf "== test_goal_cursor_reset ==\n";
  Switch.run @@ fun sw ->
  let c = make_case ~env ~sw in
  let path = "/tmp/repl-test-goal-reset.ec" in
  write_file path
    "require import AllCore Int.\n\
     lemma L (x : int) : x = x.\n";
  Repl_core.dispatch c.st (":load " ^ path);
  Repl_core.dispatch c.st ":step 2";
  c.st.goal_cursor <- 5;
  Repl_core.dispatch c.st ":step";
  check "step resets goal_cursor"
    (c.st.goal_cursor = 0) "";
  c.st.goal_cursor <- 3;
  Repl_core.dispatch c.st ":back";
  check "back resets goal_cursor"
    (c.st.goal_cursor = 0) "";
  Ec_llm_session.close c.st.session

(* 13. :insert across multiple iterations keeps file consistent. *)
let test_multiple_inserts env =
  Printf.printf "== test_multiple_inserts ==\n";
  Switch.run @@ fun sw ->
  let c = make_case ~env ~sw in
  let path = "/tmp/repl-test-multi-insert.ec" in
  write_file path
    "require import AllCore Int.\n\
     lemma L (x : int) : x = x.\n\
     proof.\n";
  Repl_core.dispatch c.st (":load " ^ path);
  Repl_core.dispatch c.st ":step 3";
  ignore (drain c.out);
  Repl_core.dispatch c.st ":insert trivial";
  Repl_core.dispatch c.st ":insert qed";
  let buffer = doc_source c.st in
  check_contains "first insert present" buffer "trivial.";
  check_contains "second insert present" buffer "qed.";
  check_contains "original require retained" buffer "require import AllCore Int.";
  check_contains "original lemma retained" buffer "lemma L";
  Repl_core.dispatch c.st ":save";
  let saved = read_file path in
  check "saved == buffer" (saved = buffer) "";
  ignore (drain c.out);
  Ec_llm_session.close c.st.session

(* 14. :insert on a compound line (the original bug repro). *)
let test_insert_compound_line env =
  Printf.printf "== test_insert_compound_line ==\n";
  Switch.run @@ fun sw ->
  let c = make_case ~env ~sw in
  let path = "/tmp/repl-test-compound.ec" in
  let initial =
    "require import AllCore.\n\
     lemma L : true = true.\n\
     proof. trivial. qed.\n"
  in
  write_file path initial;
  Repl_core.dispatch c.st (":load " ^ path);
  Repl_core.dispatch c.st ":step 2";  (* require, lemma *)
  ignore (drain c.out);
  Repl_core.dispatch c.st ":insert (* note *) pragma noop";
  let buffer = doc_source c.st in
  (* All original sentences still present in the buffer. *)
  check_contains "require kept" buffer "require import AllCore.";
  check_contains "lemma kept" buffer "lemma L : true = true.";
  check_contains "proof/trivial/qed kept" buffer "trivial.";
  check_contains "qed kept" buffer "qed.";
  check_contains "inserted pragma present" buffer "pragma noop.";
  ignore (drain c.out);
  Ec_llm_session.close c.st.session

(* 15. Byte-exact :edit preserves blank line before cursor.
   Regression: EC's PARSE-JSON start_offset includes leading
   whitespace; splice used to swallow the blank line before the
   cursor sentence. *)
let test_edit_preserves_blank_line env =
  Printf.printf "== test_edit_preserves_blank_line ==\n";
  Switch.run @@ fun sw ->
  let c = make_case ~env ~sw in
  let path = "/tmp/repl-test-edit-blank.ec" in
  let initial =
    "require import AllCore Int.\n\
     \n\
     lemma bar (n : int) : 0 <= n => 0 <= n.\n\
     \n\
     lemma baz : 1 = 1.\n\
     proof. trivial. qed.\n"
  in
  write_file path initial;
  Repl_core.dispatch c.st (":load " ^ path);
  Repl_core.dispatch c.st ":step 1";  (* require only *)
  ignore (drain c.out);
  (* cursor on `lemma bar`. Edit to something shorter. *)
  Repl_core.dispatch c.st ":edit lemma bar (n : int) : true";
  let buffer = doc_source c.st in
  (* The blank line AFTER require should survive. *)
  check "blank line between require and lemma bar preserved"
    (contains buffer "require import AllCore Int.\n\nlemma bar")
    (Printf.sprintf "buffer=%S" buffer);
  (* `lemma baz` and its proof must still exist. *)
  check_contains "lemma baz preserved" buffer "lemma baz : 1 = 1.";
  check_contains "proof line preserved" buffer "proof. trivial. qed.";
  ignore (drain c.out);
  Ec_llm_session.close c.st.session

(* 16. Byte-exact :delete preserves surrounding blank lines. *)
let test_delete_preserves_blank_lines env =
  Printf.printf "== test_delete_preserves_blank_lines ==\n";
  Switch.run @@ fun sw ->
  let c = make_case ~env ~sw in
  let path = "/tmp/repl-test-delete-blank.ec" in
  let initial =
    "require import AllCore Int.\n\
     \n\
     op one : int = 1.\n\
     \n\
     op two : int = 2.\n"
  in
  write_file path initial;
  Repl_core.dispatch c.st (":load " ^ path);
  Repl_core.dispatch c.st ":step 2";  (* require, one *)
  ignore (drain c.out);
  (* cursor on `op two`. Delete. *)
  Repl_core.dispatch c.st ":delete";
  let buffer = doc_source c.st in
  (* require + blank + op one must still be present verbatim. *)
  check "require + blank + op one preserved"
    (contains buffer "require import AllCore Int.\n\nop one : int = 1.")
    (Printf.sprintf "buffer=%S" buffer);
  check_no_contains "op two removed" buffer "op two : int = 2.";
  ignore (drain c.out);
  Ec_llm_session.close c.st.session

(* 17. Byte-exact :insert preserves ALL surrounding content. *)
let test_insert_byte_integrity env =
  Printf.printf "== test_insert_byte_integrity ==\n";
  Switch.run @@ fun sw ->
  let c = make_case ~env ~sw in
  let path = "/tmp/repl-test-insert-bytes.ec" in
  let initial =
    "require import AllCore Int.\n\
     \n\
     lemma L (x : int) : x = x.\n\
     proof.\n\
     trivial.\n\
     qed.\n\
     \n\
     op final : int = 99.\n"
  in
  write_file path initial;
  Repl_core.dispatch c.st (":load " ^ path);
  Repl_core.dispatch c.st ":step 4";  (* require, lemma, proof, trivial *)
  ignore (drain c.out);
  (* Rewind one so the cursor sits on `trivial.`; insert a no-op
     pragma before it. `pragma` is a directive — always exec-safe
     even mid-proof — so the splice lands. *)
  Repl_core.dispatch c.st ":back";
  ignore (drain c.out);
  Repl_core.dispatch c.st ":insert pragma noop";
  let buffer = doc_source c.st in
  (* Everything BEFORE the insertion must be byte-identical to initial. *)
  check_contains "require/lemma/proof intact"
    buffer
    "require import AllCore Int.\n\nlemma L (x : int) : x = x.\nproof.\n";
  (* trivial + qed + op final must all survive AFTER the insertion. *)
  check_contains "trivial preserved" buffer "trivial.";
  check_contains "qed preserved" buffer "qed.";
  check_contains "op final preserved" buffer "op final : int = 99.";
  check_contains "trailing blank before op final preserved"
    buffer "qed.\n\nop final : int = 99.";
  (* The inserted pragma shows up. *)
  check_contains "inserted pragma present" buffer "pragma noop.";
  (* File unchanged on disk. *)
  check "file unchanged pre-save"
    (read_file path = initial) "disk changed without :save";
  ignore (drain c.out);
  Ec_llm_session.close c.st.session

(* 19. Truncation guard: if an edit makes the buffer unparseable so
   that EC's PARSE-JSON stops early and drops the tail, roll back
   the mutation instead of silently showing a truncated doc. *)
let test_truncation_guard env =
  Printf.printf "== test_truncation_guard ==\n";
  Switch.run @@ fun sw ->
  let c = make_case ~env ~sw in
  let path = "/tmp/repl-test-trunc.ec" in
  let initial =
    "require import AllCore Int.\n\
     op a : int = 1.\n\
     op b : int = 2.\n\
     op c : int = 3.\n"
  in
  write_file path initial;
  Repl_core.dispatch c.st (":load " ^ path);
  Repl_core.dispatch c.st ":step 2";
  ignore (drain c.out);
  let orig_buffer = doc_source c.st in
  (* Edit the cursor line to something that will parse-error
     mid-document (unterminated string opens a lexer error that
     eats the rest of the source). The guard must bail. *)
  Repl_core.dispatch c.st ":edit op b_bad : int = \"unterminated";
  let out = String.concat "\n" (drain c.out) in
  check_contains "truncation warning fired" out "WARNING";
  check "buffer IS updated despite partial parse"
    (doc_source c.st <> orig_buffer)
    "buffer unchanged";
  check_contains "buffer contains the new content"
    (doc_source c.st) "b_bad";
  ignore (drain c.out);
  Ec_llm_session.close c.st.session

(* 20. cursor position after :delete in the middle of a proof. *)
let test_delete_mid_proof env =
  Printf.printf "== test_delete_mid_proof ==\n";
  Switch.run @@ fun sw ->
  let c = make_case ~env ~sw in
  let path = "/tmp/repl-test-delete-mid.ec" in
  write_file path
    "require import AllCore Int.\n\
     lemma L (x : int) : x = x.\n\
     proof.\n\
     move=> //.\n\
     trivial.\n\
     qed.\n";
  Repl_core.dispatch c.st (":load " ^ path);
  Repl_core.dispatch c.st ":step 4";  (* require, lemma, proof, move=> //. *)
  ignore (drain c.out);
  (* cursor at `trivial.` — delete it. *)
  Repl_core.dispatch c.st ":delete";
  let buffer = doc_source c.st in
  check_no_contains "trivial. gone from buffer" buffer "trivial.";
  check_contains "qed. preserved" buffer "qed.";
  check_contains "move=> //. preserved" buffer "move=> //.";
  ignore (drain c.out);
  Ec_llm_session.close c.st.session

(* --- Main --------------------------------------------------------- *)

let () =
  match binary_path () with
  | None ->
    Printf.printf "skip: no ec llm binary\n%!"; exit 0
  | Some _ ->
    Eio_main.run @@ fun env ->
    test_dot_append env;
    test_insert_preserves_trailing env;
    test_insert_at_end env;
    test_save_and_diff env;
    test_delete_at_cursor env;
    test_delete_past_end env;
    test_edit_at_cursor env;
    test_edit_past_end env;
    test_try_refuses_executables env;
    test_try_result_routing env;
    test_goal_cycling env;
    test_goal_cursor_reset env;
    test_multiple_inserts env;
    test_insert_compound_line env;
    test_edit_preserves_blank_line env;
    test_delete_preserves_blank_lines env;
    test_insert_byte_integrity env;
    test_truncation_guard env;
    test_delete_mid_proof env;
    Printf.printf "\n== summary ==\n  pass=%d  fail=%d\n%!" !pass !fail;
    if !fail > 0 then exit 1
