(* -------------------------------------------------------------------- *)
open EcSymbols
open EcAst
open EcCoreGoal.FApi

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

(* The facts of the rule, on the probabilities of one procedure [f], from
   one initial memory [&m] and with the same arguments [args]; [Pr[E]]
   stands for [Pr[f(args) @ &m : E]], the events are read in the final
   memory [&m'] of [f] (bound by each probability). *)
type pr_fact =
  | PFMuEq       of ss_inv * ss_inv
      (* mu_eq [E1; E2]:
           (forall &m', E1 <=> E2) => (Pr[E1] = Pr[E2]) = true *)
  | PFMuSub      of ss_inv * ss_inv
      (* mu_sub [E1; E2]:
           (forall &m', E1 => E2) => (Pr[E1] <= Pr[E2]) = true *)
  | PFMuFalse    of memory
      (* mu_false [&m']:  Pr[false] = 0%r *)
  | PFMuNot      of ss_inv
      (* mu_not [E]:  Pr[!E] = Pr[true] - Pr[E] *)
  | PFMuOr       of [`Sym | `Asym] * ss_inv * ss_inv
      (* mu_or [E1; E2]:
           Pr[E1 \/ E2] = Pr[E1] + Pr[E2] - Pr[E1 /\ E2]
         ([||] instead of [\/] for [`Asym]) *)
  | PFMuDisj     of [`Sym | `Asym] * ss_inv * ss_inv
      (* mu_disjoint [E1; E2]:
           (forall &m', !(E1 /\ E2)) => Pr[E1 \/ E2] = Pr[E1] + Pr[E2]
         ([||] instead of [\/] for [`Asym]) *)
  | PFMuSplit    of ss_inv * ss_inv
      (* mu_split [E; B]:  Pr[E] = Pr[E /\ B] + Pr[E /\ !B] *)
  | PFMuGe0      of ss_inv
      (* mu_ge0 [E]:  (0%r <= Pr[E]) = true *)
  | PFMuLe1      of ss_inv
      (* mu_le1 [E]:  (Pr[E] <= 1%r) = true *)
  | PFMuSum      of ss_inv * EcIdent.t
      (* muE [E; x]:  Pr[E] = sum (fun x => Pr[E /\ res = x])
         ([E /\ res = x] simplified to [res = x] when [E] is [true]) *)
  | PFMu1LeEqMu1 of ss_inv * form * EcIdent.t * form
      (* mu1_le_eq_mu1 [e; k; k'; d]:
              phoare [f : true ==> true] = 1%r
           => (forall k', Pr[e = k'] <= mu1 d k')
           => Pr[e = k] = mu1 d k *)
  | PFMuHasLe    of ss_inv * EcIdent.t
      (* mu_has_le [has P s; x]:
           Pr[has P s] <= BRA.big predT (fun x => Pr[P x]) s *)

type pr_fact_node = {
  pfn_mem  : memory;          (* initial memory &m *)
  pfn_fun  : EcPath.xpath;    (* procedure f *)
  pfn_args : form;            (* arguments args *)
  pfn_fact : pr_fact;         (* the fact and its parameters *)
}

(* [t_bdhoare_pr_fact n] — the axiom schema of the facts on
   probabilities, [F] the fact of [n] (above):

     ---------  (no premise)
         F

   Side conditions (otherwise fails): the events of [mu_eq], [mu_sub],
   [mu_or], [mu_disjoint] and [mu_split] are in the same memory; in
   [mu1_le_eq_mu1], [k] does not depend on the memory of the event [e],
   and [k'] is free neither in [args], [e] nor [d]; in [muE] (resp.
   [mu_has_le]), [x] is free neither in [args] nor [E] (resp. [P]); the
   event of [mu_has_le] has the form [has P s], [s] not depending on the
   memory of the event; the goal is [F] (syntactically).

   Node: [RBdHoarePrFact n]. Checker: "bdhoare-pr-fact". *)
val t_bdhoare_pr_fact : pr_fact_node -> backward

(* ==================================================================== *)
(* Derived tactics                                                      *)

(* [t_pr_rewrite (s, a)] — [rewrite Pr s a]: selects in the goal the
   first subterm the lemma [s] applies to, among
   - [mu_eq] (resp. [mu_sub]): [Pr[E1] = Pr[E2]] (resp. [<=]), the same
     procedure, arguments and initial memory on both sides;
   - [mu_false], [mu_not], [mu_or], [mu_disjoint]: [Pr[false]],
     [Pr[!E]], [Pr[E1 \/ E2]] (or [||]);
   - [mu_split] (argument [B]), [muE]: any [Pr[E]];
   - [mu_ge0], [mu_le1]: [0%r <= Pr[E]], [Pr[E] <= 1%r];
   - [mu1_le_eq_mu1] (argument [d], not depending on its memory):
     [Pr[e = k]], [k] not depending on the memory of the event;
   - [mu_has_le]: [Pr[has P s]] on the left of [<=], [s] not depending
     on the memory of the event;
   resolves the parameters of the fact [F] of the lemma for it (an
   argument [B] being read in the memory of the event), and rewrites
   the goal (left to right) with the cut [F], closed on the spot by
   [t_bdhoare_pr_fact]. Visible goals: the hypotheses of [F] (none, one
   for [mu_eq], [mu_sub], [mu_disjoint], two for [mu1_le_eq_mu1]), then
   the rewritten goal, as for [rewrite] with a lemma. Fails when [s] is
   not one of these lemmas, when an argument is given to a lemma that
   takes none (or conversely), or when no subterm matches. Emits no node
   of its own. *)
val t_pr_rewrite : symbol * ss_inv option -> backward

(* ==================================================================== *)
(* Elaboration                                                          *)

(* [rewrite Pr s [a]]: [t_pr_rewrite], the argument [a] typed in the final
   memory of the selected probability (with the type [bool] for
   [mu_split], [ty distr] for [mu1_le_eq_mu1], [ty] the type of [k]). *)
val process_pr_rewrite : symbol * EcParsetree.pformula option -> backward
