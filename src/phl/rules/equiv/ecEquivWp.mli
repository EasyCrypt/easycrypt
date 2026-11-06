(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcCoreGoal.FApi
open EcMatching.Position

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

type equiv_wp = {
  ewp_uselet : bool;   (* let-bind the substitutions of the wp *)
}

(* [t_equiv_wp { ewp_uselet = b }] — weakest precondition:

     ---------------------------------------------  c, c' wp-able
     equiv [c ~ c' : wp<2>(c', wp<1>(c, Q)) ==> Q]

   where [wp<i>] is [EcPlWp.wp] on side [i]: [c] and [c'] are made of
   assignments, [if] and [match] only. No premise. Side conditions: [c] and
   [c'] are entirely wp-able, and the goal's precondition is convertible to
   [wp<2>(c', wp<1>(c, Q))] (otherwise fails).

   Node: [REquivWp { ewp_uselet = b }]. Checker: "equiv-wp". *)
val t_equiv_wp : equiv_wp -> backward

(* ==================================================================== *)
(* Derived tactics                                                      *)

(* [t_equiv_wp_full ?uselet (k, k')] — the surface [wp], on the goal
   [equiv [c ~ c' : P ==> Q]], with [c = c1; c2] and [c' = c1'; c2'] where
   [c2 = c[k..)] and [c2' = c'[k'..)] when the positions are given (they
   must then be entirely wp-able: otherwise fails with "remaining n
   instruction(s)") and the longest wp-able suffixes otherwise. Expands to:

   1. [EcEquivSeq.t_equiv_seq] at [(|c1|, |c1'|)], with the relation
        R := wp<2>(c2', wp<1>(c2, Q))
      giving  (a) equiv [c1 ~ c1' : P ==> R]     — left open,
              (b) equiv [c2 ~ c2' : R ==> Q];
   2. [t_equiv_wp] closes (b).

   Visible goal: (a). Emits no node of its own. *)
val t_equiv_wp_full : ?uselet:bool -> codegap1 pair option -> backward

(* ==================================================================== *)
(* Elaboration                                                          *)

(* [wp] / [wp k k'] on an [equivS] goal: no position or a pair of them
   (typed in the ambient environment). Applies [t_equiv_wp_full]. *)
val process_equiv_wp : pdocodegap1 -> backward
