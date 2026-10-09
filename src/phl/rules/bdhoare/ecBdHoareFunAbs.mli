(* -------------------------------------------------------------------- *)
open EcParsetree
open EcCoreGoal.FApi
open EcPath
open EcAst
open EcEnv

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

type bdhoare_fun_abs = {
  bhfa_inv : ss_inv;   (* invariant I *)
}

(* [t_bdhoareF_abs { bhfa_inv = I }] — an abstract procedure that is
   lossless when its oracles are, preserves with probability 1 an invariant
   its oracles preserve with probability 1:

     forall (O1 <: T1 {-A}) ... (On <: Tn {-A}),
       islossless o_1 => ... => islossless o_k => islossless A(O1..On).g
     phoare [o_1 : I ==> I] >= 1%r   ...   phoare [o_k : I ==> I] >= 1%r
     ------------------------------------------------------------------
                      phoare [f : I ==> I] >= 1%r

   where [f] is [A(...).g], [o_1 ... o_k] the oracles [f] may call ([o_i]
   in the first premise being the corresponding procedure of the [Oj]).
   Side conditions: [f] (normalized) is a procedure of an abstract module
   [A], [I] does not depend on [glob A], no oracle [o_i] accesses [glob A],
   and the goal is exactly [phoare [f : I ==> I] >= 1%r] (the bound
   syntactically [1%r]) (otherwise fails).

   Node: [RBdHoareFunAbs { bhfa_inv = I }]. Checker: "bdhoareF-fun-abs". *)
val t_bdhoareF_abs : bdhoare_fun_abs -> backward

(* [bdhoareF_abs_spec env f I] is [(I, I, premises)]: the pre- and
   postcondition of the conclusion of [t_bdhoareF_abs], and its premises.
   Fails if [f] is not abstract, [I] depends on its globals or an oracle
   accesses them. *)
val bdhoareF_abs_spec : env -> xpath -> ss_inv -> ss_inv * ss_inv * form list

(* ==================================================================== *)
(* Derived tactics                                                      *)

(* [t_bdhoareF_abs_full { bhfa_inv = I }] — on [phoare [f : P ==> Q] ~ 1%r]
   ([~] being [>=] or [=], the bound syntactically [1%r]; fails otherwise):
   - for [>=]: the consequence rule (currently
     [EcPhlConseq.t_bdHoareF_conseq]) to [phoare [f : I ==> I] >= 1%r],
     then [t_bdhoareF_abs] on it. Visible goals: the two side conditions of
     the consequence ([P => I], [I => Q]), the losslessness premise, then
     [phoare [o_i : I ==> I] >= 1%r] for each oracle;
   - for [=]: the bound-changing consequence (currently
     [EcPhlConseq.t_bdHoareF_conseq_bd]) to [>= 1%r], whose side condition
     is closed by [trivial], then the [>=] case; each oracle premise is
     turned back into [phoare [o_i : I ==> I] = 1%r] by the bound-changing
     consequence, its side condition closed by [trivial]. Visible goals:
     as for [>=], with [= 1%r] oracle premises.
   Emits no node of its own. *)
val t_bdhoareF_abs_full : bdhoare_fun_abs -> backward

(* ==================================================================== *)
(* Elaboration                                                          *)

(* [proc I] on a [bdhoareF] goal for an abstract procedure: [I] is typed as
   a boolean formula in a memory [&hr]. Applies [t_bdhoareF_abs_full]. *)
val process_bdhoareF_abs : pformula -> backward
