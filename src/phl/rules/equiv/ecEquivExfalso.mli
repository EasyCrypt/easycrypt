(* -------------------------------------------------------------------- *)
open EcCoreGoal.FApi

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

(* [t_equivS_exfalso] — false precondition:

     ------------------------------
     equiv [c ~ c' : false ==> Q]

   No premise. Side condition: the precondition is syntactically [false]
   (otherwise fails).

   Node: [REquivSExfalso]. Checker: "equivS-exfalso". *)
val t_equivS_exfalso : backward

(* [t_equivF_exfalso] — same for procedures:

     ------------------------------
     equiv [f ~ f' : false ==> Q]

   Node: [REquivFExfalso]. Checker: "equivF-exfalso". *)
val t_equivF_exfalso : backward
