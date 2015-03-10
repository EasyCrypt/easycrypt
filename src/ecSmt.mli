(* -------------------------------------------------------------------- *)
open EcFol
open EcEnv
open EcProvers

(* -------------------------------------------------------------------- *)
val check : ?notify:notify -> prover_infos -> LDecl.hyps -> form -> bool
