(* -------------------------------------------------------------------- *)
open EcParsetree
open EcCoreGoal.FApi
open EcMatching.Position

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

type bdhoare_wp_rule = {
  bwr_at     : codegap1 option;   (* split position k; none: see below *)
  bwr_uselet : bool;              (* let-bind the substitutions of the wp *)
}

(* [t_bdhoare_wp { bwr_at = k; bwr_uselet = b }] — weakest precondition of
   a suffix, with [~] the goal's comparison:

        phoare [c1 : P ==> wp(c2, Q)] ~ d
     ---------------------------------------  c = c1; c2   (c1 = c[0..k))
             phoare [c : P ==> Q] ~ d          c2 wp-able

   where [wp(c2, Q)] is [EcPlWp.wp]: [c2] is made of assignments, [if] and
   [match] only, hence deterministic and terminating — which is what makes
   the rule sound for every comparison and bound. Without [k], [c2] is the
   longest wp-able suffix of [c]. Side condition: [c2] is entirely wp-able
   (otherwise fails with "remaining n instruction(s)").

   This rule is still stated over [c1; c2], with an implicit [seq]: the
   bdhoare [seq] rule ([EcBdHoareSeq.t_bdhoare_seq]) has extra premises
   (invariant, event, bounds, non-modification) whose discharge would
   require more trusted rules for [c2] and real arithmetic, so it cannot
   reproduce this rule's single premise as a derived composition.

   Node: [RBdHoareWp { bwn_at = |c1| (resolved index); bwn_uselet = b }].
   Checker: "bdhoare-wp". *)
val t_bdhoare_wp : bdhoare_wp_rule -> backward

(* ==================================================================== *)
(* Elaboration                                                          *)

(* [wp] / [wp k] on a [bdHoareS] goal: no position or a single one (typed
   in the ambient environment). Applies [t_bdhoare_wp]. *)
val process_bdhoare_wp : pdocodegap1 -> backward
