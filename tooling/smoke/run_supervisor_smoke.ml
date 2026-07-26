(** Phase 2 supervisor-fiber smoke. Spawns a session, SIGKILLs its
    [ec llm] subprocess externally, asserts the supervisor fires
    [session.crashed] via the on-crash callback within a deadline. *)

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

let () =
  match binary_path () with
  | None ->
    Printf.printf "skip: no ec llm binary found (set EC_LLM_BIN)\n%!";
    exit 0
  | Some bin ->
    Eio_main.run @@ fun env ->
    let crash_seen : (string * string) option ref = ref None in
    Transcript.configure (Transcript.devnull ());
    Ec_llm_session.configure
      ~process_mgr:(Eio.Stdenv.process_mgr env)
      ~executable:bin
      ~extra_args:[ "-I"; Filename.concat (Sys.getcwd ()) "theories" ] ();
    Ec_llm_session.configure_on_crash
      (fun ~label ~exit_kind -> crash_seen := Some (label, exit_kind));

    let pass = ref true in
    let check label cond detail =
      if cond then Printf.printf "  ok  %s\n%!" label
      else begin
        Printf.printf "  FAIL %s — %s\n%!" label detail;
        pass := false
      end
    in

    Switch.run (fun sw ->
      let s = Ec_llm_session.start ~sw ~label:"crash-test" in
      let pid = Ec_llm_session.pid s in
      check "pid is positive" (pid > 0)
        (Printf.sprintf "got pid=%d" pid);
      (* Kill the subprocess externally (not via cancel/close) so the
         supervisor fiber observes an unsolicited exit. *)
      Unix.kill pid Sys.sigkill;
      (* Wait up to 5s for the supervisor to record the crash. *)
      let clock = Eio.Stdenv.clock env in
      let deadline = Eio.Time.now clock +. 5.0 in
      let rec wait () =
        if !crash_seen <> None then ()
        else if Eio.Time.now clock > deadline then ()
        else begin
          Eio.Time.sleep clock 0.05;
          wait ()
        end
      in
      wait ();
      (match !crash_seen with
       | Some (label, kind) ->
         check "supervisor fired session.crashed"
           (label = "crash-test" && String.length kind > 0)
           (Printf.sprintf "label=%s kind=%s" label kind);
         check "exit_kind is signal:9 for SIGKILL"
           (kind = "signal:9")
           (Printf.sprintf "got %s" kind)
       | None ->
         check "supervisor fired session.crashed" false
           "callback never invoked within 5s deadline"));

    (* Suppression check: a [close]-initiated teardown must NOT fire
       the crash callback. Reset state, run a fresh session, close it
       cleanly, assert silence. *)
    crash_seen := None;
    Switch.run (fun sw ->
      let s = Ec_llm_session.start ~sw ~label:"clean-close" in
      Ec_llm_session.close s;
      (* Give the supervisor a beat to (not) fire. *)
      let clock = Eio.Stdenv.clock env in
      Eio.Time.sleep clock 0.5;
      check "close suppresses session.crashed"
        (!crash_seen = None)
        (match !crash_seen with
         | Some (l, k) -> Printf.sprintf "fired with label=%s kind=%s" l k
         | None -> ""));

    Printf.printf "\n== supervisor smoke ==\n";
    Printf.printf "  pass=%b\n%!" !pass;
    exit (if !pass then 0 else 1)
