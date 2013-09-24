(* -------------------------------------------------------------------- *)
open EcParsetree
open EcFol
open EcBaseLogic
open EcLogic

(* -------------------------------------------------------------------- *)
class rn_hl_while : form -> form option -> (form * form) option ->
object
  inherit xrule
end

(* -------------------------------------------------------------------- *)
val t_hoare_while      : form -> tactic
val t_bdHoare_while    : form -> form -> tactic
val t_equiv_while_disj : bool -> form -> form -> tactic
val t_equiv_while      : form -> tactic

(* -------------------------------------------------------------------- *)
val process_while : bool option -> pformula -> pformula option -> tactic
val process_while : bool option -> pformula -> pformula option -> 
  (pformula * pformula) option -> tactic
