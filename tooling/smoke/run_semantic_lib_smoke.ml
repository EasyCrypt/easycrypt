(** Unit smokes for the semantic-edit shared-lib modules:
    [Goal_view], [Speculation], [Fuzzy_filter], [Search_result].
    Spawned session exercised only by the Speculation test. *)

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

(* --- Goal_view ------------------------------------------------------ *)

let test_goal_view () =
  Printf.printf "== Goal_view ==\n%!";
  (* Conclusion is now a structured tree (UPSTREAM #23). v0 emits
     a `pp` leaf for non-judgment conclusions like `1 = 1`. *)
  let json = {|
    {"active":true,"subgoal_count":1,"current_index":0,
     "subgoals":[
       {"index":0,
        "hypotheses":[
          {"name":"H","kind":"hyp","pp":"1 = 1"},
          {"name":"x","kind":"var","pp":"int"}],
        "conclusion":{"kind":"pp","text":"1 = 1"}}]}
  |} in
  match Goal_view.of_string json with
  | Error e -> check "decode" false e
  | Ok gv ->
    check "active" gv.active "active=false";
    check "subgoal_count" (gv.subgoal_count = 1) "wrong count";
    (match Goal_view.focused gv with
     | None -> check "focused" false "no focused subgoal"
     | Some sg ->
       check "two hyps" (List.length sg.hypotheses = 2) "wrong hyp count";
       check "conclusion is pp leaf"
         (match sg.conclusion with Cn_pp _ -> true | _ -> false)
         "expected Cn_pp leaf";
       check "conclusion text" (Goal_view.to_pp_text sg.conclusion = "1 = 1")
         (Printf.sprintf "got %S" (Goal_view.to_pp_text sg.conclusion));
       match sg.hypotheses with
       | [h; x] ->
         check "hyp name" (h.name = "H") h.name;
         check "hyp kind" (h.kind = Hyp) (Goal_view.hyp_kind_to_string h.kind);
         check "var name" (x.name = "x") x.name;
         check "var kind" (x.kind = Var) (Goal_view.hyp_kind_to_string x.kind)
       | _ -> check "hyp list" false "wrong shape");
  (* Inactive payload *)
  (match Goal_view.of_string {|{"active":false,"subgoal_count":0,"current_index":0,"subgoals":[]}|} with
   | Error e -> check "inactive decode" false e
   | Ok gv ->
     check "inactive.active" (not gv.active) "should be inactive";
     check "inactive focused" (Goal_view.focused gv = None) "should be None");

  (* of_json . to_json round-trip on the rich payload. *)
  (match Goal_view.of_string json with
   | Error e -> check "round-trip: initial decode" false e
   | Ok gv1 ->
     let encoded = Goal_view.to_json gv1 in
     match Goal_view.of_json encoded with
     | Error e -> check "round-trip: re-decode" false e
     | Ok gv2 ->
       check "round-trip: active preserved" (gv1.active = gv2.active) "";
       check "round-trip: subgoal_count preserved"
         (gv1.subgoal_count = gv2.subgoal_count) "";
       check "round-trip: current_index preserved"
         (gv1.current_index = gv2.current_index) "";
       check "round-trip: subgoals length preserved"
         (List.length gv1.subgoals = List.length gv2.subgoals) "";
       (match gv1.subgoals, gv2.subgoals with
        | [sg1], [sg2] ->
          check "round-trip: subgoal index preserved"
            (sg1.index = sg2.index) "";
          check "round-trip: conclusion preserved (flattened)"
            (Goal_view.to_pp_text sg1.conclusion
             = Goal_view.to_pp_text sg2.conclusion) "";
          check "round-trip: hypothesis count preserved"
            (List.length sg1.hypotheses = List.length sg2.hypotheses) "";
          (match sg1.hypotheses, sg2.hypotheses with
           | [h1a; h1b], [h2a; h2b] ->
             check "round-trip: hyp names preserved"
               (h1a.name = h2a.name && h1b.name = h2b.name) "";
             check "round-trip: hyp kinds preserved"
               (h1a.kind = h2a.kind && h1b.kind = h2b.kind) "";
             check "round-trip: hyp pp preserved"
               (h1a.pp = h2a.pp && h1b.pp = h2b.pp) ""
           | _ -> check "round-trip: hyp shape" false "")
        | _ -> check "round-trip: subgoal shape" false ""))

(* --- Fuzzy_filter --------------------------------------------------- *)

let test_fuzzy_filter () =
  Printf.printf "\n== Fuzzy_filter ==\n%!";
  let items = [ "addzC"; "addz0"; "mulzC"; "congr"; "addrA"; "absz" ] in
  let by_name s = s in

  let r = Fuzzy_filter.filter "add" items ~key:by_name in
  let names = List.map (fun (m : string Fuzzy_filter.match_result) -> m.item) r in
  check "add: filters to addXXX"
    (List.for_all (fun n -> String.length n >= 3 && String.sub n 0 3 = "add") names
     && List.length names = 3)
    (Printf.sprintf "got %s" (String.concat ", " names));

  let r2 = Fuzzy_filter.filter "z0" items ~key:by_name in
  let names2 = List.map (fun (m : string Fuzzy_filter.match_result) -> m.item) r2 in
  check "z0: subsequence"
    (List.mem "addz0" names2)
    (Printf.sprintf "got %s" (String.concat ", " names2));

  let r3 = Fuzzy_filter.filter "" items ~key:by_name in
  check "empty query: all items kept"
    (List.length r3 = List.length items) "items dropped on empty query";

  let r4 = Fuzzy_filter.filter "XYZ" items ~key:by_name in
  check "no-match query: empty result"
    (List.length r4 = 0) "unexpected matches"

(* --- Search_result -------------------------------------------------- *)

let test_search_result () =
  Printf.printf "\n== Search_result ==\n%!";
  let notices = [
    "(* Int.addz0 *)";
    "lemma addz0:";
    "  forall (x : int), x + 0 = x.";
    "(* Int.addzC *)";
    "lemma addzC: forall (x y : int), x + y = y + x.";
  ] in
  let hits = Search_result.of_notices notices in
  check "two hits" (List.length hits = 2)
    (Printf.sprintf "got %d" (List.length hits));
  (match hits with
   | [h1; h2] ->
     check "h1 qname" (h1.qname = "Int.addz0") h1.qname;
     check "h1 kind" (h1.kind = "lemma") h1.kind;
     check "h1 short" (h1.short_name = "addz0") h1.short_name;
     check "h1 sig contains forall"
       (String.length h1.signature >= 10
        && (try ignore (Str.search_forward (Str.regexp_string "forall") h1.signature 0); true
            with Not_found -> false))
       h1.signature;
     check "h2 qname" (h2.qname = "Int.addzC") h2.qname;
     check "h2 short" (h2.short_name = "addzC") h2.short_name
   | _ -> check "hit count" false "wrong shape");
  (* Stray pre-marker lines dropped *)
  let noisy = ["random preamble"; "(* A.B *)"; "lemma x: true."] in
  let hits2 = Search_result.of_notices noisy in
  check "ignores pre-marker noise" (List.length hits2 = 1)
    (Printf.sprintf "got %d" (List.length hits2));
  (* Unmarked decl-heads also count — EC emits them for directly-
     accessible hits (no theory qualification needed). Parser keys
     them by short name. *)
  let no_markers = ["lemma x:"; "true."] in
  let bare_hits = Search_result.of_notices no_markers in
  check "unmarked decl-head is also a hit"
    (List.length bare_hits = 1)
    (Printf.sprintf "got %d hits" (List.length bare_hits));
  (match bare_hits with
   | [h] ->
     check "unmarked qname defaults to short name" (h.qname = "x") h.qname
   | _ -> check "bare hit structure" false "wrong shape");

  (* Back-to-back unmarked decls split correctly. *)
  let multi =
    [ "lemma foo: forall x, x."
    ; "lemma bar: forall y, y."
    ; "axiom baz: true."
    ]
  in
  check "consecutive unmarked decls split"
    (List.length (Search_result.of_notices multi) = 3)
    (Printf.sprintf "got %d" (List.length (Search_result.of_notices multi)))

(* --- Speculation --------------------------------------------------- *)

let test_speculation ~bin env =
  Printf.printf "\n== Speculation ==\n%!";
  Switch.run @@ fun sw ->
  let process_mgr = Eio.Stdenv.process_mgr env in
  Ec_llm_session.configure ~process_mgr
    ~executable:bin
    ~extra_args:[ "-I"; Filename.concat (Sys.getcwd ()) "theories" ] ();
  let s = Ec_llm_session.start ~sw ~label:"spec" in
  let feed src cls =
    let corr = Correlation.of_client "feed" in
    match Ec_llm_session.exec s ~corr ~sentence_class:cls ~source:src with
    | Ok _ -> ()
    | Error e ->
      Printf.eprintf "feed failed: %s\n%!" (Error.to_string e); exit 1
  in
  feed "require import AllCore." `Executable;
  feed "lemma _spec_smoke : 1 = 1." `Executable;
  feed "proof." `Executable;
  let pre = Ec_llm_session.current_uuid s in

  (* Capture, run reflexivity, rollback — uuid should be restored *)
  let h = Speculation.capture s in
  check "captured uuid" (Speculation.captured_uuid h = pre)
    (Printf.sprintf "captured %d vs current %d" (Speculation.captured_uuid h) pre);
  let corr = Correlation.of_client "spec-try" in
  let r =
    Ec_llm_session.exec_json s ~corr
      ~command_json:{|{"kind":"tactic","name":"reflexivity","args":[]}|}
  in
  (match r with
   | Ok ok ->
     check "speculative exec advanced uuid" (ok.replied_uuid > pre)
       (Printf.sprintf "%d !> %d" ok.replied_uuid pre)
   | Error e -> check "speculative exec ok" false (Error.to_string e));
  (match Speculation.rollback s h with
   | Ok () ->
     check "rollback restored uuid" (Ec_llm_session.current_uuid s = pre)
       (Printf.sprintf "%d != %d" (Ec_llm_session.current_uuid s) pre)
   | Error e -> check "rollback ok" false (Error.to_string e));

  (* Second try on the same session post-rollback: should work. *)
  let h2 = Speculation.capture s in
  let r2 =
    Ec_llm_session.exec_json s ~corr
      ~command_json:{|{"kind":"tactic","name":"trivial","args":[]}|}
  in
  check "second try after rollback" (match r2 with Ok _ -> true | Error _ -> false)
    (match r2 with Ok _ -> "" | Error e -> Error.to_string e);
  check "commit returns captured uuid"
    (Speculation.commit h2 = pre)
    (Printf.sprintf "commit %d vs pre %d" (Speculation.commit h2) pre);

  Ec_llm_session.close s

(* --- Main ---------------------------------------------------------- *)

let () =
  test_goal_view ();
  test_fuzzy_filter ();
  test_search_result ();
  (match binary_path () with
   | None ->
     Printf.printf "\n== Speculation ==\n  skip: no ec llm binary found (set EC_LLM_BIN)\n%!"
   | Some bin ->
     Eio_main.run (fun env -> test_speculation ~bin env));
  Printf.printf "\n== summary ==\n";
  Printf.printf "  pass=%d  fail=%d\n%!" !pass !fail;
  exit (if !fail = 0 then 0 else 1)
