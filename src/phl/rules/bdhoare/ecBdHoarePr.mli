(* -------------------------------------------------------------------- *)
open EcCoreGoal.FApi

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

(* [t_bdhoareF_pr] — a probabilistic judgement on a procedure from the
   probability of its postcondition, with [~] the goal's comparison:

     forall &m, 0%r <= d /\ (P => Pr[f(args) @ &m : Q] [~] d)
     -------------------------------------------------------
                  phoare [f : P ==> Q] ~ d

   where [args] are the arguments of [f] read in [&m], and [x [~] d] is
   [x <= d] for [<=], [x = d] for [=] and [d <= x] for [>=].

   Node: [RBdHoareFPr]. Checker: "bdhoareF-pr". *)
val t_bdhoareF_pr : backward
