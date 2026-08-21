(* -------------------------------------------------------------------- *)
(* Model Context Protocol server over stdio: a second front-end, next to
   the [easycrypt llm] REPL, over the shared engine core in
   [EcLlmCore]. Driven via the [easycrypt mcp] command. *)

(* Serve JSON-RPC 2.0 messages on stdin/stdout until end of input, then
   exit the process. Never returns. [projini] resolves the
   [easycrypt.project] context of a file path, as for the REPL. *)
val run :
     relocdir:string option
  -> boot:bool
  -> projini:(string option -> EcOptions.ini_context option)
  -> EcOptions.mcp_option
  -> 'a
