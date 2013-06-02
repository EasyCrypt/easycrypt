(* -------------------------------------------------------------------- *)
open EcParsetree
open EcFol
open EcBaseLogic

(* -------------------------------------------------------------------- *)
val process_phl_formula  : EcEnv.env -> goal -> pformula -> form
val process_prhl_formula : EcEnv.env -> goal -> pformula -> form

val process_phl : EcLocation.t -> EcEnv.env -> phltactic -> goal -> goals
