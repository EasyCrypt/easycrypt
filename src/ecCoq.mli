(* -------------------------------------------------------------------- *)
open EcFol
open EcEnv
open EcProvers

(* -------------------------------------------------------------------- *)
val check :
     loc:EcLocation.t
  -> name:string
  -> ?notify:notify
  -> prover_infos
  -> ?coqmode:coq_mode
  -> LDecl.hyps
  -> form
  -> bool
