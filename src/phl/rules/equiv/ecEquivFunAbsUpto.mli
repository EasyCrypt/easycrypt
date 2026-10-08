(* -------------------------------------------------------------------- *)
open EcParsetree
open EcCoreGoal
open EcCoreGoal.FApi
open EcAst

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

type equiv_fun_abs_upto = {
  efu_ll   : bool;     (* lossless variant ([proc @[ll]]) *)
  efu_bad  : ss_inv;   (* bad event B, read on the right *)
  efu_inv  : ts_inv;   (* invariant P, while B does not hold *)
  efu_binv : ts_inv;   (* invariant Q, once B holds *)
}

(* [t_equivF_abs_upto { efu_ll = false; efu_bad = B; efu_inv = P;
                        efu_binv = Q }] — two instances of the same abstract
   procedure, equivalent up to the bad event [B]:

     forall (O1 <: T1 {-A}) ... (On <: Tn {-A}),
       islossless o_1 => ... => islossless o_k => islossless A(O1..On).g
     for each pair of oracles (o_i, o'_i):
       equiv [o_i ~ o'_i : !B{2} /\ ={arg} /\ P
                       ==> if B{2} then Q else ={res} /\ P]
       forall &2, B{2} => phoare [o_i : Q ==> Q] = 1%r
       forall &1, phoare [o'_i : B /\ Q ==> B /\ Q] = 1%r
     -----------------------------------------------------------------
     equiv [f ~ f' : if B{2} then Q else ={arg} /\ ={glob A} /\ P
                 ==> if B{2} then Q else ={res} /\ ={glob A} /\ P]

   where [f] is [A(O..).g] and [f'] is [A(O'..).g] (normalized, the same
   procedure [g] of the same abstract module [A]), [o_i] / [o'_i] are the
   oracles they may call, pairwise ([o_i] in the first premise being the
   corresponding procedure of the [Oj]); in the per-oracle phoare premises,
   the other memory is the quantified one ([if B{2} then ...] is
   simplified when [B] is [true] or [false]). With [efu_ll = true], the
   first premise is [islossless f] and [islossless f'], and the two phoare
   premises of each oracle are the corresponding hoare judgements
   [hoare [o_i : Q ==> Q]] and [hoare [o'_i : B /\ Q ==> B /\ Q]].
   Side conditions: [f] and [f'] are procedures of the same abstract module
   [A], [B], [P] and [Q] do not depend on [glob A] (on either side), no
   oracle accesses [glob A], and the goal is exactly the conclusion above
   (otherwise fails).

   Node: [REquivFunAbsUpto { efu_ll; efu_bad = B; efu_inv = P;
   efu_binv = Q }]. Checker: "equivF-fun-abs-upto". *)
val t_equivF_abs_upto : equiv_fun_abs_upto -> backward

(* ==================================================================== *)
(* Derived tactics                                                      *)

(* [t_equivF_abs_upto_full r] — on [equiv [f ~ f' : P' ==> Q']]:
   1. the consequence rule (currently [EcPhlConseq.t_equivF_conseq]) to the
      conclusion of [t_equivF_abs_upto r];
   2. then [t_equivF_abs_upto r] on it.
   Visible goals: the two side conditions of the consequence, then the
   premises of the rule. Emits no node of its own. *)
val t_equivF_abs_upto_full : equiv_fun_abs_upto -> backward

(* ==================================================================== *)
(* Elaboration                                                          *)

(* Types the arguments of [proc @[ll] B P Q] (also used by [call]): [B] in
   a memory [&hr], [P] and [Q] in memories [&1] and [&2], [Q] defaulting to
   [true]; the lossless variant is selected by [@[ll]]. *)
val process_equivF_abs_upto_info : fun_upto_info -> tcenv1 -> equiv_fun_abs_upto

(* [proc @[ll] B P Q] on an [equivF] goal for an abstract procedure.
   Applies [t_equivF_abs_upto_full]. *)
val process_equivF_abs_upto : fun_upto_info -> backward
