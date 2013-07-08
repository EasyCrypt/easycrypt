(* -------------------------------------------------------------------- *)
open EcParsetree
open EcFol
open EcLogic

(* -------------------------------------------------------------------- *)
val process_phl_form     : EcTypes.ty -> goal -> pformula -> form
val process_phl_formula  : goal -> pformula -> form
val process_prhl_formula : goal -> pformula -> form

val process_phl : EcLocation.t -> phltactic -> goal -> goals
