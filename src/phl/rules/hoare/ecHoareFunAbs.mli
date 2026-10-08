(* -------------------------------------------------------------------- *)
open EcParsetree
open EcCoreGoal.FApi
open EcPath
open EcAst
open EcEnv

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

type hoare_fun_abs = {
  hfa_inv : ss_inv;   (* invariant I *)
}

(* [t_hoareF_abs { hfa_inv = I }] — an abstract procedure preserves an
   invariant its oracles preserve:

     hoare [o_1 : I ==> I]   ...   hoare [o_k : I ==> I]
     --------------------------------------------------  f = A(...).g abstract
                   hoare [f : I ==> I]                  I independent of glob A

   where [o_1 ... o_k] are the oracles [f] may call. The judgements carry
   no exceptional postcondition: an exception listed by no branch is
   unconstrained (#1188), so the conclusion holds for instances of [A] and
   oracles that raise. Side conditions: [f] (normalized) is a procedure of
   an abstract module [A], [I] does not depend on [glob A], and the goal is
   exactly [hoare [f : I ==> I]] (otherwise fails).

   Node: [RHoareFunAbs { hfa_inv = I }]. Checker: "hoareF-fun-abs". *)
val t_hoareF_abs : hoare_fun_abs -> backward

(* [hoareF_abs_spec env f I] is [(I, I, premises)]: the pre- and
   postcondition of the conclusion of [t_hoareF_abs], and its premises.
   Fails if [f] is not abstract or [I] depends on its globals. *)
val hoareF_abs_spec : env -> xpath -> ss_inv -> ss_inv * ss_inv * form list

(* ==================================================================== *)
(* Derived tactics                                                      *)

(* [t_hoareF_abs_full { hfa_inv = I }] — on [hoare [f : P ==> Q | E]]:
   1. the consequence rule (currently [EcPhlConseq.t_hoareF_conseq]) to
      [hoare [f : I ==> I]];
   2. then [t_hoareF_abs] on it.
   Visible goals: the two side conditions of the consequence ([P => I],
   and [I => Q] together with the exceptional postconditions [E]), then
   [hoare [o_i : I ==> I]] for each oracle. Emits no node of its own. *)
val t_hoareF_abs_full : hoare_fun_abs -> backward

(* ==================================================================== *)
(* Elaboration                                                          *)

(* [proc I] on a [hoareF] goal for an abstract procedure: [I] is typed as a
   boolean formula in a memory [&hr]. Applies [t_hoareF_abs_full]. *)
val process_hoareF_abs : pformula -> backward
