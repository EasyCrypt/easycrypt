(* -------------------------------------------------------------------- *)
open EcParsetree
open EcCoreGoal.FApi
open EcMatching.Position

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

type hoare_wp = {
  hwp_uselet : bool;   (* let-bind the substitutions of the wp *)
}

(* [t_hoare_wp { hwp_uselet = b }] — weakest precondition:

     -----------------------------------  c wp-able
     hoare [c : wp(c, Q | E) ==> Q | E]

   where [wp(c, Q | E)] is [EcPlWp.wp ~onesided:true]: [c] is made of
   assignments, [if], [match] and [raise] only (a [raise e] has the
   exceptional postcondition [E_e] as wp). No premise. Side conditions:
   [c] is entirely wp-able, and the goal's precondition is convertible to
   [wp(c, Q | E)] (otherwise fails).

   Node: [RHoareWp { hwp_uselet = b }]. Checker: "hoare-wp". *)
val t_hoare_wp : hoare_wp -> backward

(* ==================================================================== *)
(* Derived tactics                                                      *)

(* [t_hoare_wp_full ?uselet k] — the surface [wp], on the goal
   [hoare [c : P ==> Q | E]], with [c = c1; c2] where [c2] is [c[k..)] when
   [k] is given (it must then be entirely wp-able: otherwise fails with
   "remaining n instruction(s)") and the longest wp-able suffix of [c]
   otherwise. Expands to:

   1. [EcHoareSeq.t_hoare_seq] at [|c1|], with the assertion
        R := wp(c2, Q | E)
      giving  (a) hoare [c1 : P ==> R | E]     — left open,
              (b) hoare [c2 : R ==> Q | E];
   2. [t_hoare_wp] closes (b).

   Visible goal: (a). Emits no node of its own. *)
val t_hoare_wp_full : ?uselet:bool -> codegap1 option -> backward

(* ==================================================================== *)
(* Elaboration                                                          *)

(* [wp] / [wp k] on a [hoareS] goal: no position or a single one (typed in
   the ambient environment). Applies [t_hoare_wp_full]. *)
val process_hoare_wp : pdocodegap1 -> backward
