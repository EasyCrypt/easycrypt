(* -------------------------------------------------------------------- *)
open EcParsetree
open EcCoreGoal.FApi

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

(* [t_bdhoare_if] — conditional, with [~] the goal's comparison ([<=],
   [=] or [>=]):

     phoare [c1 : P /\ b ==> Q] ~ d      phoare [c2 : P /\ !b ==> Q] ~ d
     ------------------------------------------------------------------
                 phoare [if b then c1 else c2 : P ==> Q] ~ d

   Side condition: the statement is the single conditional (otherwise
   fails).

   Node: [RBdHoareIf]. Checker: "bdhoare-if". *)
val t_bdhoare_if : backward

(* ==================================================================== *)
(* Derived tactics                                                      *)

(* [t_bdhoare_if_head] — on [phoare [if b then c1 else c2; c : P ==> Q] ~ d]:
   1. when [c] is not empty, [EcBdHoareTransform.t_bdhoare_transform]
      with [EcTrIfPush.TrIfPush], giving
        phoare [if b then { c1; c } else { c2; c } : P ==> Q] ~ d;
   2. [t_bdhoare_if].
   Visible goals: phoare [c1; c : P /\ b ==> Q] ~ d and
   phoare [c2; c : P /\ !b ==> Q] ~ d. Fails if the first instruction is
   not a conditional. Emits no node of its own. *)
val t_bdhoare_if_head : backward

(* ==================================================================== *)
(* Elaboration                                                          *)

(* [if] on a [bdHoareS] goal: applies [t_bdhoare_if_head]. The side, if
   any, is ignored (behaviour preserved). The [seq]-ing forms are
   rejected: they expect an [equivS] goal. *)
val process_bdhoare_if : pcond_info -> backward
