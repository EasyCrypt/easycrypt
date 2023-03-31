(* -------------------------------------------------------------------- *)
open EcParsetree
open EcCoreGoal.FApi

(* -------------------------------------------------------------------- *)
(* Transitivity rule for equiv
 *
 *
 *  1.  forall m1 m2 m3, Q1 m1 m2 => Q2 m2 m3 => Q m1 m3
 *  2.  c1 ~ c2 : P1 ==> Q1
 *  3.  c2 ~ c3 : P2 ==> Q2
 *  --------------------------------------------------------
 *      c1 ~ c3 : P ==> Q

 * The most basic rule is normally:
 *         Q = exists m2, Q1 m1 m2 /\ Q2 m2 m3
 *
 * The actual rule is in this core rule + conseq.
 *)


(* -------------------------------------------------------------------- *)
val t_equivS_trans :
     EcMemory.memtype * EcModules.stmt
  -> EcFol.form * EcFol.form
  -> EcFol.form * EcFol.form
  -> EcCoreGoal.FApi.backward

val t_equivF_trans :
     EcPath.xpath
  -> EcFol.form * EcFol.form
  -> EcFol.form * EcFol.form
  -> EcCoreGoal.FApi.backward

(* -------------------------------------------------------------------- *)
val process_equiv_trans :
  trans_kind * trans_formula -> backward
