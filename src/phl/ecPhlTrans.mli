(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2015 - IMDEA Software Institute
 * Copyright (c) - 2012--2015 - Inria
 * 
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

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
val process_equiv_trans :
  trans_kind * pformula * pformula * pformula * pformula -> backward
