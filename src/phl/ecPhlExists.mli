(* -------------------------------------------------------------------- *)
open EcParsetree
open EcFol
open EcBaseLogic
open EcLogic

(* -------------------------------------------------------------------- *)
class rn_hl_exists_elim : object
  inherit xrule
end

(* -------------------------------------------------------------------- *)
val t_hr_exists_elim  : tactic
val t_hr_exists_intro : form list -> tactic

(* -------------------------------------------------------------------- *)
val process_exists_intro : pformula list -> tactic
