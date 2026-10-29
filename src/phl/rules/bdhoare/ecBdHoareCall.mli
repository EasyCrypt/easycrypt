(* -------------------------------------------------------------------- *)
open EcParsetree
open EcCoreGoal
open EcCoreGoal.FApi
open EcAst

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

(* The bdhoare [call] rule is kept with its historical statement, on
   [c; lv <@ f(a)]: an implicit [seq] before the call and an implicit
   framing of the prefix's postcondition over [mod f], the variables
   written by [f]. Its [seq] could not be made explicit with
   [EcBdHoareSeq.t_bdhoare_seq] without changing its premises: that rule
   also bounds the runs of the prefix ending outside the intermediate
   assertion (premises (G1) / (G2), the bound (B)), and asks that the
   prefix does not change the bound of the suffix (N), which this rule
   does not state (the second is a side condition here). *)

type bdhoare_call = {
  bhcall_pre  : ss_inv;          (* precondition P of the procedure *)
  bhcall_post : ss_inv;          (* postcondition Q of the procedure *)
  bhcall_bd   : ss_inv option;   (* bound b of the procedure, if not d *)
}

(* [t_bdhoare_call { bhcall_pre = P; bhcall_post = Q; bhcall_bd = ob }] —
   call, [~] the goal's comparison and [d] its bound:

     phoare [f : P ==> Q] ~ b         (b := ob when given, d otherwise)
     J [c : P0 ==> P[arg := a] /\ W]
     -------------------------------------------------
     phoare [c; lv <@ f(a) : P0 ==> R] ~ d

     W := forall result, forall (mod f), C[res := result, lv := result]

   where [/\] is the asymmetric conjunction [&&], built with the
   simplifying constructors, and, by cases on [~ d] and [ob]:

       ~ d             ob          C            J [c : P0 ==> X]
       <= d            none        R => Q       hoare  [c : P0 ==> X]
       = d             none        Q <=> R [1]  phoare [c : P0 ==> X] = 1
       >= d            none        Q => R       phoare [c : P0 ==> X] = 1
       = d / >= d      some b      as above     phoare [c : P0 ==> X] ~ d / b

   [1] [R => Q] when [d] is syntactically [0%r], [Q => R] when it is
   [1%r]. Side conditions, in order (each failing with its message): the
   last instruction is a call; [b] does not depend on local variables
   (it is read in the memory of [f], with the locals of the callee) nor
   on the variables written by [c] (#1189); [ob] is not given for [<=].

   Composite statement (implicit [seq] and framing, see above). Soundness:
   with [ob = Some b], the runs of [c] ending outside [P[arg := a] /\ W]
   are not accounted for, and [d / b] is [0] for [b = 0]: the conclusion
   does not follow for [=], nor for [>=] when [b <= 0]. This form is not
   reachable from the surface tactics, which never give [ob].

   Node: [RBdHoareCall { bhcall_pre = P; bhcall_post = Q; bhcall_bd = ob }].
   Checker: "bdhoare-call". *)
val t_bdhoare_call : bdhoare_call -> backward

(* ==================================================================== *)
(* Elaboration                                                          *)

(* The cut of [call] on a [bdHoareS] goal, as [(spec, t)]: [spec] is the
   specification of the procedure [f] called last, with the comparison and
   bound of the goal, [t] the tactic run on it once the cut is applied.
   - [call (_ : P ==> Q)] (no side): [P] and [Q] typed in the memory of
     [f]; [spec] is [phoare [f : P ==> Q] ~ d], [t] the identity;
   - [call (: I)] (no side): [I] typed in an abstract memory (global
     variables only); [spec] is [phoare [f : I ==> I] ~ d], [t] is
     [proc I] (or [proc] for a concrete [f], see [EcPhlFun.t_fun])
     followed by [trivial] on its first two goals;
   - [call (: bad, P, Q)]: fails (an equiv is expected). *)
val process_bdhoare_call_cut :
  oside -> call_info -> tcenv1 -> EcFol.form * backward
