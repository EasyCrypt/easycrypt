(* -------------------------------------------------------------------- *)
open EcCoreGoal.FApi

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

(* None: the hoare [pr] tactic is derived from the bdhoare one. *)

(* ==================================================================== *)
(* Derived tactics                                                      *)

(* [t_hoareF_pr] — on [hoare [f : P ==> Q]]:
   1. [EcHoareOfBdHoare.t_hoareF_of_bdhoare], to
      [phoare [f : P ==> !Q] = 0%r];
   2. then [EcBdHoarePr.t_bdhoareF_pr].
   Visible goal:
     [forall &m, 0%r <= 0%r /\ (P => Pr[f(args) @ &m : !Q] = 0%r)].
   Emits no node of its own. *)
val t_hoareF_pr : backward
