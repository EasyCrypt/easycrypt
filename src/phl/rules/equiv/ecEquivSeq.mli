(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcCoreGoal.FApi
open EcMatching.Position
open EcAst

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

type equiv_seq_rule = {
  esr_at  : codegap1 pair;   (* split positions (k, k') *)
  esr_mid : ts_inv;          (* intermediate relation R *)
}

(* [t_equiv_seq { esr_at = (k, k'); esr_mid = R }] — sequence:

       equiv [c1 ~ c1' : P ==> R]      equiv [c2 ~ c2' : R ==> Q]
     ------------------------------------------------------------  c  = c1; c2   (c1  = c [0..k ))
                     equiv [c ~ c' : P ==> Q]                     c' = c1'; c2' (c1' = c'[0..k'))

   Node: [REquivSeq { esn_at = (k, k') (resolved indices); esn_mid = R }].
   Checker: "equiv-seq". *)
val t_equiv_seq : equiv_seq_rule -> backward

(* ==================================================================== *)
(* Derived tactics                                                      *)

(* [t_equiv_seq_onesided `Left k pre post] — one-sided sequence on the goal
   [equiv [c1; c2 ~ c' : P ==> Q]], with [c1 = c[0..k)] (symmetrically for
   [`Right]). Expands to:

   1. [t_equiv_seq] at [(k, end)], with the relation
        R := pre<1> /\ forall (mod c2)<1>, post<1> => Q
      giving  (a) equiv [c1 ~ c' : P ==> R]          — left open,
              (b) equiv [c2 ~ skip : R ==> Q];
   2. on (b), the framed consequence (currently [EcPhlConseq.t_equivS_conseq_nm])
      to [equiv [c2 ~ skip : pre<1> ==> post<1>]]; its side conditions
      [R => pre<1>] and [R => forall (mod c2)<1>, post<1> => Q] are closed
      by [t_trivial];
   3. then [EcPhlConseq.t_equivS_conseq_bd] to
        (c) phoare [c2 : pre ==> post] = 1%r          — left open.

   Visible goals: (a) and (c). Emits no node of its own. *)
val t_equiv_seq_onesided : side -> codegap1 -> ss_inv -> ss_inv -> backward

(* ==================================================================== *)
(* Elaboration                                                          *)

(* On an [equivS] goal, no bound information:
   - [seq k k' : R] (no side, single relation): applies [t_equiv_seq]; both
     positions are typed in the left memory (behaviour preserved);
   - [seq{i} k : (pre ==> post)] (side required): applies
     [t_equiv_seq_onesided]. *)
val process_equiv_seq : seq_info -> backward
