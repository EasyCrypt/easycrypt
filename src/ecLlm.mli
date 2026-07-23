(* -------------------------------------------------------------------- *)
(* The LLM coding-agent REPL: an interactive proof-development protocol
   over stdin/stdout. Driven via the [easycrypt llm] command. *)

(* Run the REPL until [QUIT] or EOF, then exit the process. Never
   returns. [projini] resolves the [easycrypt.project] context of a
   file path, so [LOAD] can apply the project's load path and prover
   options the way the batch compiler does. *)
val run :
     relocdir:string option
  -> boot:bool
  -> projini:(string option -> EcOptions.ini_context option)
  -> EcOptions.llm_option
  -> 'a
