(* -------------------------------------------------------------------- *)
open EcTypes
open EcFol
open EcBaseLogic
open EcLogic

(* -------------------------------------------------------------------- *)
class rn_hl_case : form ->
object
  inherit xrule

  method phi : form
end

(* -------------------------------------------------------------------- *)
val t_hoare_case   : form -> tactic
val t_bdHoare_case : form -> tactic
val t_equiv_case   : form -> tactic

val t_hl_case : form -> tactic
