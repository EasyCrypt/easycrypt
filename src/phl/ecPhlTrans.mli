(* -------------------------------------------------------------------- *)
open EcMemory
open EcParsetree
open EcModules
open EcFol
open EcBaseLogic
open EcLogic

(* -------------------------------------------------------------------- *)
class rn_equiv_trans : object
  inherit xrule
end

(* -------------------------------------------------------------------- *)
module Low : sig
  val t_equivS_trans :
    memtype * stmt -> form -> form -> form -> form -> tactic

  val t_equivF_trans :
    EcPath.xpath -> form -> form -> form -> form -> tactic
end

(* -------------------------------------------------------------------- *)
val process_equiv_trans :
  trans_kind * pformula * pformula * pformula * pformula -> tactic
