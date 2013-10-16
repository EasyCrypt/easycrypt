(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcBaseLogic
open EcLogic

(* -------------------------------------------------------------------- *)
class rn_eqobs_in : object
  inherit xrule
end

(* -------------------------------------------------------------------- *)
val process_eqobs_in : pformula option tuple3 -> tactic
