(** Standalone debug: run a search pattern against a live ec llm and
    print raw notices + parsed hits for side-by-side comparison.
    Usage:  EC_LLM_BIN=./ec.native dune exec tooling/smoke/run_search_debug.exe -- "(_ + _)" *)

open Ecd_core
open Eio.Std

let () =
  if Array.length Sys.argv < 2 then begin
    Printf.eprintf "usage: run_search_debug <pattern>\n%!";
    exit 2
  end;
  let pattern = Sys.argv.(1) in
  let bin =
    match Sys.getenv_opt "EC_LLM_BIN" with
    | Some p -> p
    | None -> Filename.concat (Sys.getcwd ()) "_build/default/src/ec.exe"
  in
  Eio_main.run @@ fun env ->
  Switch.run @@ fun sw ->
  Transcript.configure (Transcript.devnull ());
  let process_mgr = Eio.Stdenv.process_mgr env in
  Ec_llm_session.configure ~process_mgr ~executable:bin
    ~extra_args:[ "-I"; Filename.concat (Sys.getcwd ()) "theories" ] ();
  let s = Ec_llm_session.start ~sw ~label:"dbg" in
  let corr = Correlation.of_client "dbg" in
  let _ = Ec_llm_session.exec s ~corr ~sentence_class:`Executable
            ~source:"require import AllCore Int." in
  let body = "search " ^ pattern ^ "." in
  Printf.printf "send: %s\n\n%!" body;
  (match Ec_llm_session.exec s ~corr ~sentence_class:`Directive ~source:body with
   | Error e ->
     Printf.printf "error: %s\n%!" (Error.to_string e)
   | Ok ok ->
     Printf.printf "=== %d raw notices ===\n%!" (List.length ok.notices);
     List.iter (fun n -> Printf.printf "  NOTICE: %s\n%!" n) ok.notices;
     Printf.printf "\n=== reply body (%d bytes) ===\n%s\n%!"
       (String.length ok.output) ok.output;
     let hits = Search_result.of_notices ok.notices in
     Printf.printf "\n=== %d parsed hits ===\n%!" (List.length hits);
     List.iter (fun (h : Search_result.hit) ->
       Printf.printf "  qname=%S  short=%S  kind=%S\n    sig: %s\n%!"
         h.qname h.short_name h.kind h.signature) hits);
  Ec_llm_session.close s
