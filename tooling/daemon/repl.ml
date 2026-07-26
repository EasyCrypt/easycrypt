(** Line-oriented frontend for [Repl_core]. Reads commands from stdin
    and prints their output directly. All command semantics live in
    [Repl_core] so the TUI can reuse them — per the TUI/REPL parity
    rule, no command lives in only one frontend. *)

open Ecd_core
open Eio.Std
module Repl_core = Ecd_core.Repl_core

let run ~bin ~extra_args =
  Eio_main.run @@ fun env ->
  Switch.run @@ fun sw ->
  Transcript.configure (Transcript.devnull ());
  let process_mgr = Eio.Stdenv.process_mgr env in
  Ec_llm_session.configure ~process_mgr ~executable:bin ~extra_args ();
  let session = Ec_llm_session.start ~sw ~label:"repl" in
  let st = Repl_core.make ~session ~sw in
  Printf.printf "ecd repl (type :help for commands, :q to exit)\n%!";
  let prompt () = Printf.printf "ec> %!" in
  try
    while true do
      prompt ();
      match input_line stdin with
      | exception End_of_file -> raise Repl_core.Quit
      | line ->
        (try Repl_core.dispatch st line with
         | Repl_core.Quit -> raise Repl_core.Quit
         | e ->
           Printf.printf "error: %s\n%!" (Printexc.to_string e))
    done
  with Repl_core.Quit ->
    Ec_llm_session.close st.session;
    Printf.printf "bye\n%!"
