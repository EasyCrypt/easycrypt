(* -------------------------------------------------------------------- *)
open EcParsetree
open EcCoreGoal.FApi
open EcAst

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

type bdhoare_rnd_rule = {
  brr_info : (ss_inv, ty -> ss_inv option, ty -> ss_inv) rnd_tac_info;
    (* the event [E : ty -> bool] and the bounds, [ty] being the type of the
       sampled values; [PTwoRndParams] is rejected *)
}

(* [t_bdhoare_rnd { brr_info }] — sampling at the end of the statement.

   UNLIKE the hoare, ehoare and equiv [rnd] rules, this rule is stated over
   [c; x <$ d], keeping the prefix [c] (an implicit [seq]): its premises are
   judgements on [c] (a hoare one, for the [<=] forms), which the bdhoare
   [seq] rule ([EcBdHoareSeq.t_bdhoare_seq]: invariant, event, four bounds,
   bound arithmetic and non-modification premises) cannot reproduce. Some
   forms also rely on [c] not writing the bound [d] (an implicit frame, see
   [d0] below).

   Below, [~] is the goal's comparison, [d] its bound, [ty] the type of the
   sampled values, [Q_v := Q[x := v]], and [C(E)] the event condition
     <=  :  forall v, E v => v \in d => Q_v
     >=  :  forall v, Q_v => v \in d => E v
     =   :  forall v, v \in d => (E v <=> Q_v)
   The rule binds [d0] as [d] itself when [c] does not write the variables
   of [d], and otherwise as a fresh real [bd], with [P0 := P /\ d = bd] and
   [forall bd] in front of the premise ([P0 := P] in the first case). When
   no event is given, it is inferred: [E := predT] when [Q] does not
   mention [x], [E := fun v => Q_v] when [x] is a variable, and the rule
   fails otherwise.

   (1) no event, [<=], [x] not in [Q]:

         phoare [c : P ==> Q] <= d
       ------------------------------
       phoare [c; x <$ d : P ==> Q] <= d

   (2) [<=], event [E] (given, or inferred and [x] in [Q]):

       hoare [c : P0 ==> mu d E <= d0 /\ C(E)]      forall &m, 0%r <= d
       ----------------------------------------------------------------
                    phoare [c; x <$ d : P ==> Q] <= d

   (3) no event, [=] or [>=], [x] not in [Q]:

       phoare [c : P ==> Q /\ mu d predT = 1%r] ~ d
       --------------------------------------------
             phoare [c; x <$ d : P ==> Q] ~ d

   (4) [=] or [>=], event [E] (given, or inferred and [x] in [Q]):

       phoare [c : P0 ==> mu d E ~ d0 /\ C(E)] ~' 1%r
       ----------------------------------------------
              phoare [c; x <$ d : P ==> Q] ~ d

       where [~'] is [~] for an inferred event, and [=] for a given one.

   (5) [phi d1 d2 d3 d4 [E]] (event inferred, [x] a variable, when absent;
       [E := fun v => Q_v] — no [predT] simplification):

       forall &m, d1 * d2 + d3 * d4 ~ d
       phoare [c : P ==> phi] ~ d1
       forall &m, phi => mu d E ~ d2 /\ C(E)
       phoare [c : P ==> !phi] ~ d3
       forall &m, !phi => mu d E ~ d4 /\ C(E)
       forall &m, 0 <= d1 <= 1 /\ 0 <= d2 <= 1 /\ 0 <= d3 <= 1 /\ 0 <= d4 <= 1
       ------------------------------------------------------------------------
                         phoare [c; x <$ d : P ==> Q] ~ d

   Premises are produced in the order displayed. Side conditions: the last
   instruction is a sampling, and an event can be inferred when needed.

   Node: [RBdHoareRnd n], with [n] the event / bounds instantiated at [ty]:
   [BRndInfer], [BRndEvent E] or [BRndSplit { brs_phi; brs_d1; ...;
   brs_event }]. Checker: "bdhoare-rnd"; it recomputes the written
   variables of [c] and the inferred event from the goal's context. *)
val t_bdhoare_rnd : bdhoare_rnd_rule -> backward

(* ==================================================================== *)
(* Derived tactics                                                      *)

(* [t_bdhoare_rnd_full r] — [t_bdhoare_rnd r], then, for forms (2), an
   attempt to close the premise [forall &m, 0%r <= d] with [t_trivial]
   (left open when it fails). Emits no node of its own. *)
val t_bdhoare_rnd_full : bdhoare_rnd_rule -> backward

(* ==================================================================== *)
(* Elaboration                                                          *)

(* [rnd], [rnd E] or [rnd phi d1 d2 d3 d4 [E]] on a [bdHoareS] goal: no
   side, no position. The event [E] is typed as a [ty -> bool] function,
   [phi] as a formula, the bounds as reals, all in the goal's memory.
   Applies [t_bdhoare_rnd_full]. *)
val process_bdhoare_rnd :
  oside -> psemrndpos option -> rnd_tac_info_f -> backward
