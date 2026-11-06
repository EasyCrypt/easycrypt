(* -------------------------------------------------------------------- *)
open EcParsetree
open EcCoreGoal.FApi
open EcMatching.Position

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

type ehoare_wp = {
  ehwp_uselet : bool;   (* let-bind the substitutions of the wp *)
}

(* [t_ehoare_wp { ehwp_uselet = b }] — weakest pre-expectation:

     ---------------------------  c wp-able
     ehoare [c : ewp(c, Q) ==> Q]

   where [ewp(c, Q)] is [EcPlWp.ewp]: [c] is made of assignments,
   samplings and [if] only (a sampling [x <$ d] has the expectation, over
   [d], of the ewp of what follows as ewp). No premise. Side conditions:
   [c] is entirely wp-able, and the goal's pre-expectation is convertible
   to [ewp(c, Q)] (otherwise fails).

   Node: [REHoareWp { ehwp_uselet = b }]. Checker: "ehoare-wp". *)
val t_ehoare_wp : ehoare_wp -> backward

(* ==================================================================== *)
(* Derived tactics                                                      *)

(* [t_ehoare_wp_full ?uselet k] — the surface [wp], on the goal
   [ehoare [c : P ==> Q]], with [c = c1; c2] where [c2] is [c[k..)] when [k]
   is given (it must then be entirely wp-able: otherwise fails with
   "remaining n instruction(s)") and the longest wp-able suffix of [c]
   otherwise. Expands to:

   1. [EcEHoareSeq.t_ehoare_seq] at [|c1|], with the expectation
        R := ewp(c2, Q)
      giving  (a) ehoare [c1 : P ==> R]     — left open,
              (b) ehoare [c2 : R ==> Q];
   2. [t_ehoare_wp] closes (b).

   Visible goal: (a). Emits no node of its own. *)
val t_ehoare_wp_full : ?uselet:bool -> codegap1 option -> backward

(* ==================================================================== *)
(* Elaboration                                                          *)

(* [wp] / [wp k] on an [eHoareS] goal: no position or a single one (typed
   in the ambient environment). Applies [t_ehoare_wp_full]. *)
val process_ehoare_wp : pdocodegap1 -> backward
