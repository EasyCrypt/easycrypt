(* -------------------------------------------------------------------- *)
open EcCoreGoal.FApi

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

(* [t_bdhoareS_of_hoare] — an event has probability 0 when its negation
   always holds:

         hoare [c : P ==> !Q]
     ----------------------------
     phoare [c : P ==> Q] = 0%r

   Side condition: the goal's bound is syntactically [= 0%r] (otherwise
   fails).

   Node: [RBdHoareSOfHoare]. Checker: "bdhoareS-of-hoare". *)
val t_bdhoareS_of_hoare : backward

(* [t_bdhoareF_of_hoare] — same for a procedure:

         hoare [f : P ==> !Q]
     ----------------------------
     phoare [f : P ==> Q] = 0%r

   Node: [RBdHoareFOfHoare]. Checker: "bdhoareF-of-hoare". *)
val t_bdhoareF_of_hoare : backward

(* ==================================================================== *)
(* Derived tactics                                                      *)

(* [t_bdhoareS_of_hoare_full] — on [phoare [c : P ==> Q] ~ d]:
   1. unless [~ d] is syntactically [= 0%r], the bound-changing consequence
      (currently [EcPhlConseq.t_bdHoareS_conseq_bd]) to
      [phoare [c : P ==> Q] = 0%r], whose side condition (relating [~ d] to
      [= 0%r]) is closed when [EcPhlAuto.t_pl_trivial] does, and left open
      otherwise;
   2. then [t_bdhoareS_of_hoare].
   Visible goals: the bound side condition if not closed, then
   [hoare [c : P ==> !Q]]. Emits no node of its own. *)
val t_bdhoareS_of_hoare_full : backward

(* [t_bdhoareF_of_hoare_full] — same for a procedure, with
   [EcPhlConseq.t_bdHoareF_conseq_bd] and [t_bdhoareF_of_hoare]. *)
val t_bdhoareF_of_hoare_full : backward
