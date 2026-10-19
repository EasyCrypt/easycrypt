(* -------------------------------------------------------------------- *)
open EcParsetree
open EcCoreGoal
open EcCoreGoal.FApi
open EcAst

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

type ehoare_call = {
  ehcall_pre  : ss_inv;   (* pre-expectation P of the procedure *)
  ehcall_post : ss_inv;   (* post-expectation Q of the procedure *)
}

(* [t_ehoare_call { ehcall_pre = P; ehcall_post = Q }] — single call:

                 ehoare [f : P ==> Q]
     ---------------------------------------------
     ehoare [lv <@ f(a) : P[arg := a] ==> Q[res := lv]]

   No framing: the post-expectation of the goal is the one of [f], with
   the result read in [lv]. Side conditions, in order: the statement is
   the single call [lv <@ f(a)]; [lv] assigns local variables only; when
   the call has no left-value, [Q] does not read [res]; the post- and the
   pre-expectation of the goal are convertible to the ones displayed
   (otherwise fails, with the historical messages of the "ehoare call core
   rule").

   Soundness: [P] and [Q] are read in the memory of [f] in the premise and
   in the memory of the goal in the conclusion; the rule is sound when they
   read no local variable other than [arg] / [res]. The specifications of
   [call (_ : P ==> Q)] and [call (: I)] are typed so; the cut of
   [call /fc] is not (see [process_ehoare_call_concave]).

   Node: [REHoareCall { ehcall_pre = P; ehcall_post = Q }].
   Checker: "ehoare-call". *)
val t_ehoare_call : ehoare_call -> backward

(* ==================================================================== *)
(* Derived tactics                                                      *)

(* [t_ehoare_call_last { ehcall_pre = P; ehcall_post = Q }] — on
   [ehoare [c; lv <@ f(a) : P0 ==> R]] (the side conditions on [lv] and
   [Q] of [t_ehoare_call] are checked first):
   1. [EcEHoareSeq.t_ehoare_seq] before the call, with intermediate
      expectation [P[arg := a]], giving
        (a) ehoare [c : P0 ==> P[arg := a]]                 — left open,
        (b) ehoare [lv <@ f(a) : P[arg := a] ==> R];
   2. [t_ehoare_call] on (b) (failing unless [R] is convertible to
      [Q[res := lv]]), giving
        (c) ehoare [f : P ==> Q]                            — left open.
   Visible goals: (c), then (a). Emits no node of its own. *)
val t_ehoare_call_last : ehoare_call -> backward

(* [t_ehoare_call_concave fc { ehcall_pre = P; ehcall_post = Q }] — on
   [ehoare [c; lv <@ f(a) : P0 ==> R]], with [fc] a function on
   expectations:
   1. [EcEHoareSeq.t_ehoare_seq] before the call, with intermediate
      expectation [fc (P[arg := a])], giving
        (a) ehoare [c : P0 ==> fc (P[arg := a])]            — left open,
        (b) ehoare [lv <@ f(a) : fc (P[arg := a]) ==> R];
   2. on (b), the concave consequence [EcPhlConseq.t_ehoareS_concave fc]
      to [ehoare [lv <@ f(a) : P[arg := a] ==> Q[res := lv]]], whose
      three side conditions are left open;
   3. [t_ehoare_call] on the latter, giving
        (c) ehoare [f : P ==> Q]                            — left open.
   Visible goals: the three side conditions of step 2, (c), then (a).
   Emits no node of its own. TEMPORARY: step 2 uses the not-yet-migrated
   [EcPhlConseq]. *)
val t_ehoare_call_concave : ss_inv -> ehoare_call -> backward

(* ==================================================================== *)
(* Elaboration                                                          *)

(* The cut of [call] on an [eHoareS] goal, as [(spec, t)]: [spec] is the
   specification of the procedure [f] called last, [t] the tactic run on it
   once the cut is applied.
   - [call (_ : P ==> Q)] (no side): [P] and [Q] typed as expectations in
     the memory of [f]; [spec] is [ehoare [f : P ==> Q]], [t] the
     identity;
   - [call (: I)] (no side): [I] typed as an expectation in an abstract
     memory (global variables only); [spec] is [ehoare [f : I ==> I]], [t]
     is [proc I] (or [proc] for a concrete [f], see [EcPhlFun.t_fun])
     followed by [trivial] on its first two goals;
   - [call (: bad, P, Q)]: fails (an equiv is expected). *)
val process_ehoare_call_cut :
  oside -> call_info -> tcenv1 -> EcFol.form * backward

(* [call /fc spec], on an [eHoareS] goal: [fc] is typed as a function on
   expectations, in the memory of the goal; [spec] is a proof term of an
   ehoare specification of the procedure called last (or a cut
   [(_ : P ==> Q)] / [(: I)], typed as for [call]: the specification in
   the memories of the procedure, the invariant in an abstract memory, so
   that the local variables of the caller are not in scope). Applies
   [t_ehoare_call_concave], closes the first of its goals with
   [EcPhlConseq.t_concave_incr] and the next two with [trivial], applies
   [spec] to (c) (running [proc I] then [trivial] for an invariant) and
   leaves (a). *)
val process_ehoare_call_concave :
  pformula * call_info gppterm -> backward
