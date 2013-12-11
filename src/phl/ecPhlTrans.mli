(* -------------------------------------------------------------------- *)
open EcMemory
open EcParsetree
open EcModules
open EcFol
open EcBaseLogic
open EcLogic

(* -------------------------------------------------------------------- *)
(* -------------------------------------------------------------------- *)
(* Transitivity rule for equiv                                          *)

(*  forall m1 m3, P m1 m3 => exists m2, P1 m1 m2 /\ P2 m2 m3
 *  forall m1 m2 m3, Q1 m1 m2 => Q2 m2 m3 => Q m1 m3
 *  c1 ~ c2 : P1 ==> Q1
 *  c2 ~ c3 : P2 ==> Q2
 *  --------------------------------------------------------
 *      c1 ~ c3 : P ==> Q
 * Remark: the most basic rule is normally 
 *   Q = exists m2, Q1 m1 m2 /\ Q2 m2 m3
 * => the actual rule is in fact this basic rule + conseq
 * I prefer this more convenient one
 *)

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
