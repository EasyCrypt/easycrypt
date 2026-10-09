(* -------------------------------------------------------------------- *)
open EcCoreGoal.FApi

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

(* [t_hoareS_exfalso] — false precondition:

     ---------------------------
     hoare [c : false ==> Q | Q_e]

   No premise. Side condition: the precondition is syntactically [false]
   (otherwise fails).

   Node: [RHoareSExfalso]. Checker: "hoareS-exfalso". *)
val t_hoareS_exfalso : backward

(* [t_hoareF_exfalso] — same for a procedure:

     ---------------------------
     hoare [f : false ==> Q | Q_e]

   Node: [RHoareFExfalso]. Checker: "hoareF-exfalso". *)
val t_hoareF_exfalso : backward
