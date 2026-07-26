(** Smoke: record a small transcript, replay it, assert every exec
    matches; then perturb one event and assert the replay detects
    the mismatch. *)

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

let write_file path content =
  let oc = open_out path in
  output_string oc content;
  close_out oc

let record_transcript ~env ~sw ~bin ~path =
  (* Point the global transcript at a fresh channel for this recording. *)
  let oc = open_out path in
  Transcript.configure (Transcript.to_channel oc);
  let process_mgr = Eio.Stdenv.process_mgr env in
  Ec_llm_session.configure
    ~process_mgr ~executable:bin
    ~extra_args:[ "-I"; Filename.concat (Sys.getcwd ()) "theories" ] ();
  let session = Ec_llm_session.start ~sw ~label:"record" in
  let feed src cls =
    let corr = Correlation.of_client "record-feed" in
    match Ec_llm_session.exec session ~corr ~sentence_class:cls ~source:src with
    | Ok _ -> ()
    | Error e ->
      Printf.eprintf "record feed failed: %s\n%!" (Error.to_string e)
  in
  (* Small recording: require import, one op, one pragma. *)
  feed "require import AllCore." `Executable;
  feed "op one : int = 1." `Executable;
  feed "pragma noop." `Directive;
  (* Mix in a structured EXEC-JSON event so the replay driver's
     exec_json dispatch path (addition 13) gets exercised. *)
  let corr = Correlation.of_client "record-exec-json" in
  (match
     Ec_llm_session.exec_json session ~corr
       ~command_json:
         {|{"kind":"directive","name":"print","args":[{"kind":"qname","value":"one"}]}|}
   with
   | Ok _ -> ()
   | Error e ->
     Printf.eprintf "record exec_json failed: %s\n%!" (Error.to_string e));
  Ec_llm_session.close session;
  close_out oc;
  (* Reset global transcript to devnull so replay doesn't re-record. *)
  Transcript.configure (Transcript.devnull ())

let () =
  match binary_path () with
  | None ->
    Printf.printf "skip: no ec llm binary found (set EC_LLM_BIN)\n%!";
    exit 0
  | Some bin ->
  Eio_main.run @@ fun env ->
  let tmp_ok = Filename.temp_file "replay_smoke_" ".jsonl" in
  let tmp_bad = Filename.temp_file "replay_smoke_bad_" ".jsonl" in
  at_exit (fun () ->
    (try Sys.remove tmp_ok with _ -> ());
    (try Sys.remove tmp_bad with _ -> ()));

  (* Phase 1: record a clean session. *)
  Switch.run (fun sw -> record_transcript ~env ~sw ~bin ~path:tmp_ok);
  let transcript_lines =
    let ic = open_in tmp_ok in
    let rec loop acc =
      match input_line ic with
      | exception End_of_file -> close_in ic; List.rev acc
      | l -> loop (l :: acc)
    in
    loop []
  in
  check "transcript has events" (transcript_lines <> []) "empty transcript";
  let has_source =
    List.exists (fun l ->
      (try
         let j = Yojson.Safe.from_string l in
         let open Yojson.Safe.Util in
         j |> member "kind" |> to_string = "session.exec"
         && (try ignore (j |> member "payload" |> member "source" |> to_string); true
             with _ -> false)
       with _ -> false))
      transcript_lines
  in
  check "session.exec carries source" has_source
    "schema extension didn't populate source field";

  (* Phase 2: replay the clean transcript, expect all matches. *)
  Switch.run (fun sw ->
    ignore sw;
    (* Replay's Switch.run is internal. *)
    Transcript.configure (Transcript.devnull ());
    let process_mgr = Eio.Stdenv.process_mgr env in
    Ec_llm_session.configure
      ~process_mgr ~executable:bin
      ~extra_args:[ "-I"; Filename.concat (Sys.getcwd ()) "theories" ] ();
    let results =
      Replay.run ~env ~options:Replay.default_options tmp_ok
    in
    let total_execs =
      List.fold_left (fun a (r : Replay.session_result) -> a + r.execs)
        0 results
    in
    let total_mismatches =
      List.fold_left
        (fun a (r : Replay.session_result) -> a + List.length r.mismatches)
        0 results
    in
    check "replay ran at least 3 execs" (total_execs >= 3)
      (Printf.sprintf "got only %d execs" total_execs);
    check "replay clean transcript: 0 mismatches" (total_mismatches = 0)
      (Printf.sprintf "got %d mismatches" total_mismatches));

  (* Phase 3: perturb one session.reply's uuid in the transcript, expect
     replay to flag mismatches. *)
  let perturbed =
    List.map (fun line ->
      try
        let j = Yojson.Safe.from_string line in
        let open Yojson.Safe.Util in
        let kind = j |> member "kind" |> to_string in
        if kind = "session.reply" then
          let payload = j |> member "payload" in
          let bumped_uuid =
            (try payload |> member "uuid" |> to_int with _ -> 0) + 999
          in
          let new_payload =
            match payload with
            | `Assoc kvs ->
              `Assoc (List.map
                        (fun (k, v) ->
                           if k = "uuid" then (k, `Int bumped_uuid) else (k, v))
                        kvs)
            | other -> other
          in
          let new_json =
            match j with
            | `Assoc kvs ->
              `Assoc (List.map
                        (fun (k, v) ->
                           if k = "payload" then (k, new_payload) else (k, v))
                        kvs)
            | _ -> j
          in
          Yojson.Safe.to_string new_json
        else line
      with _ -> line)
      transcript_lines
  in
  write_file tmp_bad (String.concat "\n" perturbed ^ "\n");

  Switch.run (fun sw ->
    ignore sw;
    Transcript.configure (Transcript.devnull ());
    let process_mgr = Eio.Stdenv.process_mgr env in
    Ec_llm_session.configure
      ~process_mgr ~executable:bin
      ~extra_args:[ "-I"; Filename.concat (Sys.getcwd ()) "theories" ] ();
    let results =
      Replay.run ~env ~options:Replay.default_options tmp_bad
    in
    let total_mismatches =
      List.fold_left
        (fun a (r : Replay.session_result) -> a + List.length r.mismatches)
        0 results
    in
    check "perturbed transcript: mismatches detected" (total_mismatches > 0)
      "replay silently passed on a perturbed transcript");

  Printf.printf "\n== replay smoke ==\n";
  Printf.printf "  pass=%d  fail=%d\n%!" !pass !fail;
  exit (if !fail = 0 then 0 else 1)
