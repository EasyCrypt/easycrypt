(** Round-trip equivalence smoke for EXEC-JSON (addition 13).

    For each v0 command, runs the same semantic operation two ways —
    text-path [`exec`] and structured [`exec_json`] — against freshly
    spawned sessions. Asserts:
    - post-exec uuid matches
    - restarted flag matches
    - reply body matches (byte-identical)

    When they disagree, the EXEC-JSON render-and-parse contract has
    drifted from the text path and needs attention. This is the
    correctness bar the UPSTREAM #13 entry commits to. *)

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

type setup = {
  (* Preface sentences to feed before the test command, text-path.
     E.g. "require import AllCore." + "lemma foo : 1 = 1." + "proof."
     to arrive at a state where [reflexivity.] applies. *)
  preface : (string * [`Executable | `Directive | `Doc_comment]) list;
  (* The command as it appears in EC source text (what the user
     would type). *)
  text : string;
  (* The structured JSON the client emits for the same command. *)
  json : string;
  (* Human-readable test label. *)
  label : string;
  (* Sentence class expected for the text-path feed (mostly to
     satisfy the session API; EXEC-JSON doesn't need this). *)
  cls : [`Executable | `Directive | `Doc_comment];
}

let feed_preface session preface =
  List.iter (fun (src, cls) ->
    let corr = Correlation.of_client "preface" in
    match Ec_llm_session.exec session ~corr ~sentence_class:cls ~source:src with
    | Ok _ -> ()
    | Error e ->
      Printf.eprintf "preface failed on %S: %s\n%!" src (Error.to_string e);
      exit 1)
    preface

let setup_session ~bin env sw =
  let process_mgr = Eio.Stdenv.process_mgr env in
  Ec_llm_session.configure ~process_mgr
    ~executable:bin
    ~extra_args:[ "-I"; Filename.concat (Sys.getcwd ()) "theories" ] ();
  Ec_llm_session.start ~sw ~label:"eqtest"

let compare_outcomes
    ~label
    (text_res  : (Session.exec_ok, Error.t) result)
    (json_res  : (Session.exec_ok, Error.t) result)
  =
  match text_res, json_res with
  | Ok t, Ok j ->
    check (label ^ " — uuid") (t.replied_uuid = j.replied_uuid)
      (Printf.sprintf "text=%d json=%d" t.replied_uuid j.replied_uuid);
    check (label ^ " — restarted") (t.restarted = j.restarted)
      (Printf.sprintf "text=%b json=%b" t.restarted j.restarted);
    check (label ^ " — body") (t.output = j.output)
      (Printf.sprintf "text=%d bytes, json=%d bytes; first diff near %S"
         (String.length t.output) (String.length j.output)
         (let min_len = min (String.length t.output) (String.length j.output) in
          let rec find i =
            if i >= min_len then i
            else if t.output.[i] <> j.output.[i] then i
            else find (i + 1)
          in
          let i = find 0 in
          if i >= min_len then ""
          else
            let lo = max 0 (i - 10) in
            let hi = min (min_len - 1) (i + 10) in
            String.sub t.output lo (hi - lo + 1)))
  | Error et, Error ej ->
    check (label ^ " — both errored") true
      (Printf.sprintf "text: %s | json: %s"
         (Error.to_string et) (Error.to_string ej))
  | Ok _, Error ej ->
    check (label ^ " — both ok") false
      (Printf.sprintf "text ok, json erred: %s" (Error.to_string ej))
  | Error et, Ok _ ->
    check (label ^ " — both ok") false
      (Printf.sprintf "json ok, text erred: %s" (Error.to_string et))

let run_case ~bin env (s : setup) =
  (* Run text path. *)
  Switch.run (fun sw ->
    let session = setup_session ~bin env sw in
    feed_preface session s.preface;
    let corr = Correlation.of_client "text" in
    let text_res =
      Ec_llm_session.exec session ~corr ~sentence_class:s.cls ~source:s.text
    in
    (* Run EXEC-JSON path on a fresh session. *)
    Switch.run (fun sw2 ->
      let session2 = setup_session ~bin env sw2 in
      feed_preface session2 s.preface;
      let corr = Correlation.of_client "json" in
      let json_res =
        Ec_llm_session.exec_json session2 ~corr ~command_json:s.json
      in
      compare_outcomes ~label:s.label text_res json_res;
      Ec_llm_session.close session2);
    Ec_llm_session.close session)

(* --- Case definitions --------------------------------------------- *)

let require_import = ("require import AllCore.", `Executable)
let lemma_trivial = ("lemma _smoke : 1 = 1.", `Executable)
let proof_ = ("proof.", `Executable)

let reflexivity_case = {
  label = "reflexivity";
  preface = [require_import; lemma_trivial; proof_];
  text = "reflexivity.";
  json = {|{"kind":"tactic","name":"reflexivity","args":[]}|};
  cls = `Executable;
}

let trivial_case = {
  label = "trivial";
  preface = [require_import; lemma_trivial; proof_];
  text = "trivial.";
  json = {|{"kind":"tactic","name":"trivial","args":[]}|};
  cls = `Executable;
}

let print_case = {
  label = "print qname";
  preface = [require_import];
  text = "print Int.";
  json = {|{"kind":"directive","name":"print","args":[{"kind":"qname","value":"Int"}]}|};
  cls = `Directive;
}

let pragma_case = {
  label = "pragma (bare name)";
  preface = [require_import];
  text = "pragma verbose.";
  json = {|{"kind":"directive","name":"pragma","args":[{"kind":"qname","value":"verbose"}]}|};
  cls = `Directive;
}

let locate_case = {
  label = "locate qname";
  preface = [require_import];
  text = "locate Int.";
  json = {|{"kind":"directive","name":"locate","args":[{"kind":"qname","value":"Int"}]}|};
  cls = `Directive;
}

let search_qname_case = {
  label = "search qname";
  preface = [require_import];
  text = "search addrA.";
  json = {|{"kind":"directive","name":"search","args":[{"kind":"qname","value":"addrA"}]}|};
  cls = `Directive;
}

let assumption_case = {
  label = "assumption (via hyp from move)";
  preface = [
    require_import;
    ("lemma _assumption_smoke : (1 = 1) => 1 = 1.", `Executable);
    proof_;
    ("move => H.", `Executable);
  ];
  text = "assumption.";
  json = {|{"kind":"tactic","name":"assumption","args":[]}|};
  cls = `Executable;
}

let apply_hyp_case = {
  label = "apply qname (hyp)";
  preface = [
    require_import;
    ("lemma _apply_smoke : (1 = 1) => 1 = 1.", `Executable);
    proof_;
    ("move => H.", `Executable);
  ];
  text = "apply H.";
  json = {|{"kind":"tactic","name":"apply","args":[{"kind":"qname","value":"H"}]}|};
  cls = `Executable;
}

let exact_hyp_case = {
  label = "exact qname (hyp)";
  preface = [
    require_import;
    ("lemma _exact_smoke : (1 = 1) => 1 = 1.", `Executable);
    proof_;
    ("move => H.", `Executable);
  ];
  text = "exact H.";
  json = {|{"kind":"tactic","name":"exact","args":[{"kind":"qname","value":"H"}]}|};
  cls = `Executable;
}

let congr_case = {
  label = "congr";
  preface = [
    require_import;
    ("lemma _congr_smoke : 1 + 1 = 1 + 1.", `Executable);
    proof_;
  ];
  text = "congr.";
  json = {|{"kind":"tactic","name":"congr","args":[]}|};
  cls = `Executable;
}

let move_case = {
  label = "move => qname";
  preface = [
    require_import;
    ("lemma _move_smoke : (1 = 1) => 1 = 1.", `Executable);
    proof_;
  ];
  text = "move => H.";
  json = {|{"kind":"tactic","name":"move","args":[{"kind":"flag","value":"=>"},{"kind":"qname","value":"H"}]}|};
  cls = `Executable;
}

let clear_case = {
  label = "clear qname";
  preface = [
    require_import;
    ("lemma _clear_smoke : (1 = 1) => (2 = 2) => 1 = 1.", `Executable);
    proof_;
    ("move => H1 H2.", `Executable);
  ];
  text = "clear H2.";
  json = {|{"kind":"tactic","name":"clear","args":[{"kind":"qname","value":"H2"}]}|};
  cls = `Executable;
}

let elim_case = {
  label = "elim qname";
  preface = [
    require_import;
    ("lemma _elim_smoke : forall (b : bool), b = b.", `Executable);
    proof_;
    ("move => b.", `Executable);
  ];
  text = "elim b.";
  json = {|{"kind":"tactic","name":"elim","args":[{"kind":"qname","value":"b"}]}|};
  cls = `Executable;
}

let case_tactic_case = {
  label = "case qname";
  preface = [
    require_import;
    ("lemma _case_smoke : forall (b : bool), b = b.", `Executable);
    proof_;
    ("move => b.", `Executable);
  ];
  text = "case b.";
  json = {|{"kind":"tactic","name":"case","args":[{"kind":"qname","value":"b"}]}|};
  cls = `Executable;
}

let rewrite_case = {
  label = "rewrite -> qname";
  preface = [
    require_import;
    ("lemma _rw_smoke : forall (x y : int), x = y => x = y.", `Executable);
    proof_;
    ("move => x y H.", `Executable);
  ];
  text = "rewrite -> H.";
  json = {|{"kind":"tactic","name":"rewrite","args":[{"kind":"flag","value":"->"},{"kind":"qname","value":"H"}]}|};
  cls = `Executable;
}

let generalize_case = {
  label = "generalize qname";
  preface = [
    require_import;
    ("lemma _gen_smoke : forall (x : int), x = x.", `Executable);
    proof_;
    ("move => x.", `Executable);
  ];
  text = "generalize x.";
  json = {|{"kind":"tactic","name":"generalize","args":[{"kind":"qname","value":"x"}]}|};
  cls = `Executable;
}

let cases = [
  reflexivity_case;
  trivial_case;
  print_case;
  pragma_case;
  locate_case;
  search_qname_case;
  assumption_case;
  apply_hyp_case;
  exact_hyp_case;
  congr_case;
  move_case;
  clear_case;
  elim_case;
  case_tactic_case;
  rewrite_case;
  generalize_case;
]

(* --- Main --------------------------------------------------------- *)

let () =
  match binary_path () with
  | None ->
    Printf.printf "skip: no ec llm binary found (set EC_LLM_BIN)\n%!";
    exit 0
  | Some bin ->
  Eio_main.run @@ fun env ->
  Transcript.configure (Transcript.devnull ());
  Printf.printf "== exec-json round-trip smoke ==\n%!";
  List.iter (run_case ~bin env) cases;
  Printf.printf "\n== summary ==\n";
  Printf.printf "  pass=%d  fail=%d\n%!" !pass !fail;
  exit (if !fail = 0 then 0 else 1)
