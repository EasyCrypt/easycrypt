(* -------------------------------------------------------------------- *)
open EcFol
open EcEnv
open EcReduction

(* -------------------------------------------------------------------- *)
val norm_cbv : reduction_info -> LDecl.hyps -> form -> form
