(* -------------------------------------------------------------------- *)
open EcCoreGoal.FApi

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

(* [t_bdhoareS_exfalso] — false precondition, with [~] the goal's
   comparison:

          forall &m, 0%r <= d
     -------------------------------
     phoare [c : false ==> Q] ~ d

   Side condition: the precondition is syntactically [false] (otherwise
   fails).

   Node: [RBdHoareSExfalso]. Checker: "bdhoareS-exfalso". *)
val t_bdhoareS_exfalso : backward

(* [t_bdhoareF_exfalso] — same for a procedure (the premise quantifies over
   the procedure's initial memory):

          forall &m, 0%r <= d
     -------------------------------
     phoare [f : false ==> Q] ~ d

   Node: [RBdHoareFExfalso]. Checker: "bdhoareF-exfalso". *)
val t_bdhoareF_exfalso : backward
