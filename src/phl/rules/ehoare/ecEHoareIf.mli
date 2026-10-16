(* -------------------------------------------------------------------- *)
open EcParsetree
open EcCoreGoal.FApi

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

(* [t_ehoare_if] — conditional:

     ehoare [c1 : (b `|` P) ==> Q]      ehoare [c2 : (!b `|` P) ==> Q]
     ------------------------------------------------------------------
                 ehoare [if b then c1 else c2 : P ==> Q]

   where [(b `|` P)] is the expectation [P] where [b] holds, [+oo]
   elsewhere. Side condition: the statement is the single conditional
   (otherwise fails).

   Node: [REHoareIf]. Checker: "ehoare-if". *)
val t_ehoare_if : backward

(* ==================================================================== *)
(* Derived tactics                                                      *)

(* [t_ehoare_if_head] — on [ehoare [if b then c1 else c2; c : P ==> Q]]:
   1. when [c] is not empty, [EcEHoareTransform.t_ehoare_transform] with
      [EcTrIfPush.TrIfPush], giving
        ehoare [if b then { c1; c } else { c2; c } : P ==> Q];
   2. [t_ehoare_if].
   Visible goals: ehoare [c1; c : (b `|` P) ==> Q] and
   ehoare [c2; c : (!b `|` P) ==> Q]. Fails if the first instruction is
   not a conditional. Emits no node of its own. *)
val t_ehoare_if_head : backward

(* ==================================================================== *)
(* Elaboration                                                          *)

(* [if] on an [eHoareS] goal: applies [t_ehoare_if_head]. The side, if
   any, is ignored (behaviour preserved). The [seq]-ing forms are
   rejected: they expect an [equivS] goal. *)
val process_ehoare_if : pcond_info -> backward
