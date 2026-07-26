(** Phase 2 differential oracle (PoC v0). Feeds a corpus file cold,
    records the full goals payload at every executable sentence,
    then reverts to the first executable sid and re-feeds the
    remainder, comparing goals at each point. Passes iff every
    (sentence_id → goals) pair matches across the two passes —
    i.e. revert-and-re-feed is indistinguishable from a cold run.

    Deliberately narrow: one small corpus, one revert point. The
    Phase 2 acceptance "differential oracle green on corpus" is a
    longer-term commitment; this is the seed. *)

open Ecd_core
open Eio.Std

let corpus =
  "require import AllCore.\n\
   op incr (n : int) : int = n + 1.\n\
   lemma l1 (n : int) : 0 <= n => 0 <= incr n.\n\
   proof. move=> h. rewrite /incr. smt(). qed.\n\
   lemma l2 (n : int) : incr n = n + 1.\n\
   proof. rewrite /incr. trivial. qed.\n"

let binary_path () =
  match Sys.getenv_opt "EC_LLM_BIN" with
  | Some p -> Some p
  | None ->
    let candidate = Filename.concat (Sys.getcwd ())
                      "_build/default/src/ec.exe" in
    if Sys.file_exists candidate then Some candidate else None

let expect_ok label = function
  | Ok x -> x
  | Error e ->
    Printf.printf "FAIL: %s: %s\n%!" label (Error.to_string e);
    exit 1

let drive_and_capture ~bin env ~label doc =
  Switch.run @@ fun sw ->
  let process_mgr = Eio.Stdenv.process_mgr env in
  Ec_llm_session.configure ~process_mgr ~executable:bin
    ~extra_args:[ "-I"; Filename.concat (Sys.getcwd ()) "theories" ] ();
  let s = Ec_llm_session.start ~sw ~label in
  let trace = ref [] in
  List.iter
    (fun (sn : Document.sentence) ->
       if sn.parsed.cls = `Meta then ()
       else
         let cls : [`Executable | `Doc_comment | `Directive] =
           match sn.parsed.cls with
           | `Executable -> `Executable
           | `Doc_comment -> `Doc_comment
           | `Directive -> `Directive
           | `Meta -> assert false
         in
         let _ok =
           expect_ok (Printf.sprintf "%s exec %s" label sn.parsed.kind)
             (Ec_llm_session.exec s
                ~corr:(Correlation.of_client label)
                ~sentence_class:cls ~source:sn.parsed.src)
         in
         let goals =
           expect_ok (Printf.sprintf "%s goals @ %s" label sn.parsed.kind)
             (Ec_llm_session.goals s)
         in
         trace := (sn.id, goals) :: !trace)
    doc.Document.sentences;
  Ec_llm_session.close s;
  List.rev !trace

(* Cold run: start, exec all, record goals. *)
let cold_run ~bin env doc =
  drive_and_capture ~bin env ~label:"cold" doc

(* Revert run: exec all first (priming), REVERT to the first
   sid, then re-exec the suffix capturing goals along the way. *)
let revert_run ~bin env doc =
  Switch.run @@ fun sw ->
  let process_mgr = Eio.Stdenv.process_mgr env in
  Ec_llm_session.configure ~process_mgr ~executable:bin
    ~extra_args:[ "-I"; Filename.concat (Sys.getcwd ()) "theories" ] ();
  let s = Ec_llm_session.start ~sw ~label:"revert" in
  let executables =
    List.filter
      (fun (sn : Document.sentence) -> sn.parsed.cls <> `Meta)
      doc.Document.sentences
  in
  let first_sid = match executables with
    | [] -> failwith "empty doc"
    | sn :: _ ->
      let cls : [`Executable | `Doc_comment | `Directive] =
        match sn.parsed.cls with
        | `Executable -> `Executable
        | `Doc_comment -> `Doc_comment
        | `Directive -> `Directive
        | `Meta -> assert false
      in
      let _ok =
        expect_ok "prime first sentence"
          (Ec_llm_session.exec s
             ~corr:(Correlation.of_client "prime")
             ~sentence_class:cls ~source:sn.parsed.src)
      in
      sn.id
  in
  let cls_of (p : Ec_llm_session.parsed_sentence) =
    match p.cls with
    | `Executable -> `Executable
    | `Doc_comment -> `Doc_comment
    | `Directive -> `Directive
    | `Meta -> assert false
  in
  (* Exec the remaining sentences once so they land in the map. *)
  List.iter
    (fun (sn : Document.sentence) ->
       if Sentence_id.equal sn.id first_sid then ()
       else
         let _ok = expect_ok (Printf.sprintf "prime %s" sn.parsed.kind)
             (Ec_llm_session.exec s
                ~corr:(Correlation.of_client "prime2")
                ~sentence_class:(cls_of sn.parsed)
                ~source:sn.parsed.src)
         in ())
    executables;
  (* Revert to the first sentence. *)
  let () = expect_ok "revert to first"
    (Ec_llm_session.revert_to s first_sid)
  in
  (* Now re-exec the suffix and record goals. The first sentence's
     goals come from the priming exec — grab them immediately after
     revert via GOALS-JSON. *)
  let trace = ref [] in
  let first_goals = expect_ok "goals after revert"
    (Ec_llm_session.goals s) in
  trace := (first_sid, first_goals) :: !trace;
  List.iter
    (fun (sn : Document.sentence) ->
       if Sentence_id.equal sn.id first_sid then ()
       else
         let _ok = expect_ok (Printf.sprintf "re-exec %s" sn.parsed.kind)
             (Ec_llm_session.exec s
                ~corr:(Correlation.of_client "re-exec")
                ~sentence_class:(cls_of sn.parsed)
                ~source:sn.parsed.src)
         in
         let goals = expect_ok "re-exec goals"
             (Ec_llm_session.goals s) in
         trace := (sn.id, goals) :: !trace)
    executables;
  Ec_llm_session.close s;
  List.rev !trace

let () =
  match binary_path () with
  | None -> Printf.printf "skip: no ec llm binary\n%!"; exit 0
  | Some bin ->
    Printf.printf "diff-oracle: bin=%s\n%!" bin;
    Eio_main.run @@ fun env ->
    (* Split once with a dedicated splitter session. *)
    let doc =
      Switch.run @@ fun sw ->
      let process_mgr = Eio.Stdenv.process_mgr env in
      Ec_llm_session.configure ~process_mgr ~executable:bin
        ~extra_args:[ "-I"; Filename.concat (Sys.getcwd ()) "theories" ] ();
      let s = Ec_llm_session.start ~sw ~label:"splitter" in
      let d = expect_ok "split corpus"
          (Document.parse s ~uri:"corpus" ~version:0 ~source:corpus) in
      Ec_llm_session.close s;
      d
    in
    Printf.printf "  corpus: %d sentences\n%!"
      (List.length doc.sentences);

    let cold_trace = cold_run ~bin env doc in
    let revert_trace = revert_run ~bin env doc in

    if List.length cold_trace <> List.length revert_trace then begin
      Printf.printf "FAIL: trace lengths differ (%d vs %d)\n%!"
        (List.length cold_trace) (List.length revert_trace);
      exit 1
    end;

    let all_match = ref true in
    List.iter2
      (fun (sid_c, goals_c) (sid_r, goals_r) ->
         if not (Sentence_id.equal sid_c sid_r) then begin
           Printf.printf "FAIL: sid mismatch: cold=%s revert=%s\n%!"
             (Sentence_id.to_string sid_c) (Sentence_id.to_string sid_r);
           all_match := false
         end
         else if goals_c <> goals_r then begin
           Printf.printf "FAIL: goals differ at %s\n  cold: %s\n  revert: %s\n%!"
             (Sentence_id.to_string sid_c) goals_c goals_r;
           all_match := false
         end)
      cold_trace revert_trace;
    if !all_match then begin
      Printf.printf "ok: differential oracle — %d (sid, goals) pairs match\n%!"
        (List.length cold_trace);
      Printf.printf "diff-oracle passed\n%!"
    end
    else exit 1
