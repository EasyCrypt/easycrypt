(* -------------------------------------------------------------------- *)
open EcParsetree
open EcCoreGoal.FApi
open EcAst

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

type equiv_deno = {
  eqd_pre  : ts_inv;    (* P, in the memories &1 &2 of the judgement *)
  eqd_post : ts_inv;    (* Q, in the same memories *)
}

(* [t_equiv_deno { eqd_pre = P; eqd_post = Q }] — two probabilities
   compared through an equivalence of the two procedures, with [~] the
   goal's comparison:

     equiv [f1 ~ f2 : P ==> Q]
     P[&1 := &n1, &2 := &n2, arg{1} := args1, arg{2} := args2]
     forall &1 &2, Q => (E1{1} [=>] E2{2})
     ---------------------------------------------------------
     Pr[f1(args1) @ &n1 : E1] [~] Pr[f2(args2) @ &n2 : E2]

   where [~] is [=] or [<=], and [E1 [=>] E2] is [E1 <=> E2] for [=] and
   [E1 => E2] for [<=]; in the third premise, [&1] and [&2] are the final
   memories of [f1] and [f2], [E1] (resp. [E2]) read in [&1] (resp.
   [&2]). Side conditions: the goal has one of the two shapes above; [P]
   and [Q] are in the same memories [&1] and [&2], which are distinct and
   do not occur free in the goal (otherwise fails).

   Node: [REquivDeno { eqd_pre = P; eqd_post = Q }].
   Checker: "equiv-deno". *)
val t_equiv_deno : equiv_deno -> backward

(* ==================================================================== *)
(* Derived tactics                                                      *)

(* [t_equiv_deno_bad P] — on
   [Pr[f1(args1) @ &n1 : E1] <= Pr[f2(args2) @ &n2 : E2]
                                + Pr[f2(args2) @ &n2 : B]]
   (the same procedure, arguments and memory in the last two
   probabilities, otherwise fails), with
   [Q = !B{2} => E1{1} => E2{2}]:
   1. transitivity ([ler_trans]) through
      [Pr[f2(args2) @ &n2 : (E2 /\ !B) \/ B]];
   2. on the first side, [t_equiv_deno { eqd_pre = P; eqd_post = Q }],
      whose third premise is closed with [upto_bad_or];
   3. on the second side, [mu_disjoint], [ler_add], [mu_sub]
      ([EcBdHoarePrFact.t_pr_rewrite]) and the lemmas [upto_bad_false],
      [upto_bad_sub], closed on the spot (by [EcLowGoal.t_trivial] for
      the inclusion of the events).
   Visible goals: the first two premises of [t_equiv_deno], in this
   order. Emits no node of its own. *)
val t_equiv_deno_bad : ts_inv -> backward

(* [t_equiv_deno_bad2 P B1] — on
   [`|Pr[f1(args1) @ &n1 : E1] - Pr[f2(args2) @ &n2 : E2]|
                                <= Pr[f2(args2) @ &n2 : B2]]
   (the same procedure, arguments and memory in the last two
   probabilities, otherwise fails), [B1] an event of [f1], with
   [Q = (B1{1} <=> B2{2}) /\ (!B2{2} => (E1{1} <=> E2{2}))]:
   1. cuts [equiv [f1 ~ f2 : P ==> Q]] and the precondition (first
      premise of [t_equiv_deno]), and introduces them;
   2. splits each probability along [B1] (resp. [B2]) with [mu_split],
      [lerr_eq] and congruence, then applies [upto2_abs], whose premises
      are closed: positivity of probabilities ([mu_false], [mu_sub]),
      [t_equiv_deno { eqd_pre = P; eqd_post = Q }] twice (premises
      closed by the cut hypotheses and [upto2_imp_bad], resp.
      [upto2_notbad]) and [mu_sub].
   Visible goals: the judgement, then the precondition. Emits no node of
   its own. *)
val t_equiv_deno_bad2 : ts_inv -> ss_inv -> backward

(* ==================================================================== *)
(* Elaboration                                                          *)

(* [byequiv pt] (resp. [byequiv (_ : P ==> Q)]), with an optional [eq]
   flag ([byequiv =>]) and an optional bad event [: B1], on a goal
   relating two probabilities; the judgement is the type of the proof
   term [pt] (resp. is cut, [P] and [Q] typed in the memories [&1] and
   [&2]); by default, [P] equates the globals the procedures read (for the
   variables [Q] reads) and their arguments with those of the goal:
   - with [: B1], on [`|Pr[...] - Pr[...]| <= Pr[...]]: by default
     [Q = (B1{1} <=> B{2}) /\ (!B{2} => (E1{1} <=> E2{2}))], the last
     equivalence replaced by the equalities of the variables it needs
     with [eq]. Applies [t_equiv_deno_bad2];
   - on [Pr[...] <= Pr[...] + Pr[...]]: by default
     [Q = !B{2} => E1{1} => E2{2}]. Applies [t_equiv_deno_bad];
   - otherwise, on [Pr[...] = Pr[...]] or [Pr[...] <= Pr[...]]: by
     default [Q = E1{1} <=> E2{2}] (or the equalities of the variables it
     needs with [eq]), resp. [Q = E1{1} => E2{2}]. Applies
     [t_equiv_deno].
   The judgement premise is closed with [pt] (resp. left as the first
   goal). For the upto-bad forms, when the judgement does not match the
   one the derived tactic needs (e.g. a default postcondition with
   [eq]), it is used through the consequence rule
   ([EcPhlConseq.t_equivF_conseq], with the judgement's own
   precondition): the implication of the preconditions is closed by
   [EcLowGoal.t_true] (the tactic fails otherwise), that of the
   postconditions is left as the last goal. *)
val process_equiv_deno :
  deno_ppterm * bool * pformula option -> backward
