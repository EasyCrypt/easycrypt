(* -------------------------------------------------------------------- *)
open EcParsetree
open EcCoreGoal.FApi
open EcPath
open EcAst
open EcEnv

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

type equiv_fun_abs = {
  efa_inv : ts_inv;   (* relational invariant I *)
}

(* [t_equivF_abs { efa_inv = I }] — two instances of the same abstract
   procedure, with oracles related by an invariant:

     equiv [o_1 ~ o'_1 : ={arg} /\ G_1 /\ I ==> ={res} /\ G_1 /\ I]
     ...
     equiv [o_k ~ o'_k : ={arg} /\ G_k /\ I ==> ={res} /\ G_k /\ I]
     ----------------------------------------------------------------
     equiv [f ~ f' : ={arg} /\ ={glob A} /\ I ==> ={res} /\ ={glob A} /\ I]

   where [f] is [A(O..).g] and [f'] is [A(O'..).g] (normalized, the same
   procedure [g] of the same abstract module [A]), [o_i] / [o'_i] are the
   oracles they may call, pairwise, and [G_i] is [={glob A}] when [o_i] or
   [o'_i] may access [glob A], nothing otherwise. Side conditions: [f] and
   [f'] are procedures of the same abstract module [A], [I] does not depend
   on [glob A] (on either side), and the goal is exactly the conclusion
   above (otherwise fails).

   Node: [REquivFunAbs { efa_inv = I }]. Checker: "equivF-fun-abs". *)
val t_equivF_abs : equiv_fun_abs -> backward

(* [equivF_abs_spec env f f' I] is [(pre, post, premises)]: the pre- and
   postcondition of the conclusion of [t_equivF_abs], and its premises.
   Fails if the procedures are not instances of the same abstract procedure
   or [I] depends on their globals. *)
val equivF_abs_spec :
  env -> xpath -> xpath -> ts_inv -> ts_inv * ts_inv * form list

(* ==================================================================== *)
(* Derived tactics                                                      *)

(* [t_equivF_abs_full { efa_inv = I }] — on [equiv [f ~ f' : P ==> Q]]:
   1. the consequence rule (currently [EcPhlConseq.t_equivF_conseq]) to the
      conclusion of [t_equivF_abs];
   2. then [t_equivF_abs] on it.
   Visible goals: the two side conditions of the consequence
   ([P => ={arg} /\ ={glob A} /\ I], [={res} /\ ={glob A} /\ I => Q]), then
   the premises of the rule, one per pair of oracles. Emits no node of its
   own. *)
val t_equivF_abs_full : equiv_fun_abs -> backward

(* ==================================================================== *)
(* Elaboration                                                          *)

(* [proc I] on an [equivF] goal for an abstract procedure: [I] is typed as
   a boolean formula in memories [&1] and [&2]. Applies
   [t_equivF_abs_full]. *)
val process_equivF_abs : pformula -> backward
