(* -------------------------------------------------------------------- *)
open EcCoreGoal.FApi

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

(* [t_hoareS_of_bdhoare] — a hoare judgement holds when its postcondition
   is reached with probability 0 on its negation:

     phoare [c : P ==> !Q] = 0%r
     ---------------------------
         hoare [c : P ==> Q]

   Side condition: the goal has no exceptional postcondition (otherwise
   fails).

   Node: [RHoareSOfBdHoare]. Checker: "hoareS-of-bdhoare". *)
val t_hoareS_of_bdhoare : backward

(* [t_hoareF_of_bdhoare] — same for a procedure:

     phoare [f : P ==> !Q] = 0%r
     ---------------------------
         hoare [f : P ==> Q]

   Node: [RHoareFOfBdHoare]. Checker: "hoareF-of-bdhoare". *)
val t_hoareF_of_bdhoare : backward
