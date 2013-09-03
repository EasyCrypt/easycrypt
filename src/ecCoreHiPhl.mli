(* -------------------------------------------------------------------- *)
open EcParsetree
open EcTypes
open EcModules
open EcFol
open EcLogic

(* -------------------------------------------------------------------- *)
val process_phl_form     : ty -> goal -> pformula -> form
val process_phl_formula  : goal -> pformula -> form

val process_prhl_form    : ty -> goal -> pformula -> form
val process_prhl_formula : goal -> pformula -> form
