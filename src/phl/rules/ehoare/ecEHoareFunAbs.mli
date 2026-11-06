(* -------------------------------------------------------------------- *)
open EcParsetree
open EcCoreGoal.FApi
open EcPath
open EcAst
open EcEnv

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

type ehoare_fun_abs = {
  ehfa_inv : ss_inv;   (* invariant I (an extended real) *)
}

(* [t_ehoareF_abs { ehfa_inv = I }] — an abstract procedure preserves an
   invariant its oracles preserve:

     ehoare [o_1 : I ==> I]   ...   ehoare [o_k : I ==> I]
     ----------------------------------------------------  f = A(...).g abstract
                   ehoare [f : I ==> I]                   I independent of glob A

   where [o_1 ... o_k] are the oracles [f] may call. Side conditions: [f]
   (normalized) is a procedure of an abstract module [A], [I] does not
   depend on [glob A], and the goal is exactly [ehoare [f : I ==> I]]
   (otherwise fails).

   Node: [REHoareFunAbs { ehfa_inv = I }]. Checker: "ehoareF-fun-abs". *)
val t_ehoareF_abs : ehoare_fun_abs -> backward

(* [ehoareF_abs_spec env f I] is [(I, I, premises)]: the pre- and
   postcondition of the conclusion of [t_ehoareF_abs], and its premises.
   Fails if [f] is not abstract or [I] depends on its globals. *)
val ehoareF_abs_spec : env -> xpath -> ss_inv -> ss_inv * ss_inv * form list

(* ==================================================================== *)
(* Derived tactics                                                      *)

(* [t_ehoareF_abs_full { ehfa_inv = I }] — on [ehoare [f : P ==> Q]]:
   1. the consequence rule (currently [EcPhlConseq.t_ehoareF_conseq]) to
      [ehoare [f : I ==> I]];
   2. then [t_ehoareF_abs] on it.
   Visible goals: the two side conditions of the consequence ([I <= P] and
   [Q <= I]), then [ehoare [o_i : I ==> I]] for each oracle. Emits no node
   of its own. *)
val t_ehoareF_abs_full : ehoare_fun_abs -> backward

(* ==================================================================== *)
(* Elaboration                                                          *)

(* [proc I] on an [ehoareF] goal for an abstract procedure: [I] is typed as
   an extended real in a memory [&hr]. Applies [t_ehoareF_abs_full]. *)
val process_ehoareF_abs : pformula -> backward
