(* -------------------------------------------------------------------- *)
(* The LLM coding-agent REPL: an interactive proof-development protocol
   over stdin/stdout. Driven via the [easycrypt llm] command. *)

(* Run the REPL until [QUIT] or EOF, then exit the process. Never
   returns. *)
val run :
     relocdir:string option
  -> boot:bool
  -> EcOptions.llm_option
  -> 'a
