(* -------------------------------------------------------------------- *)
open EcParsetree
open EcCoreGoal.FApi

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

(* [t_hoare_if] — conditional:

     hoare [c1 : P /\ b ==> Q | E]      hoare [c2 : P /\ !b ==> Q | E]
     --------------------------------------------------------------------
                  hoare [if b then c1 else c2 : P ==> Q | E]

   Side condition: the statement is the single conditional (otherwise
   fails).

   Node: [RHoareIf]. Checker: "hoare-if". *)
val t_hoare_if : backward

(* ==================================================================== *)
(* Derived tactics                                                      *)

(* [t_hoare_if_head] — on [hoare [if b then c1 else c2; c : P ==> Q | E]]:
   1. when [c] is not empty, [EcHoareTransform.t_hoare_transform] with
      [EcTrIfPush.TrIfPush], giving
        hoare [if b then { c1; c } else { c2; c } : P ==> Q | E];
   2. [t_hoare_if].
   Visible goals: hoare [c1; c : P /\ b ==> Q | E] and
   hoare [c2; c : P /\ !b ==> Q | E]. Fails if the first instruction is
   not a conditional. Emits no node of its own. *)
val t_hoare_if_head : backward

(* ==================================================================== *)
(* Elaboration                                                          *)

(* [if] on a [hoareS] goal: applies [t_hoare_if_head]. The side, if any,
   is ignored (behaviour preserved). The [seq]-ing forms ([if _ _ : R],
   [if := R], [if{i} : (_ : P ==> Q)]) are rejected: they expect an
   [equivS] goal. *)
val process_hoare_if : pcond_info -> backward
