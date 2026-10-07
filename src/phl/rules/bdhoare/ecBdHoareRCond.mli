(* -------------------------------------------------------------------- *)
open EcParsetree
open EcCoreGoal.FApi
open EcMatching.Position

(* ==================================================================== *)
(* Derived tactics                                                      *)

type bdhoare_rcond_rule = {
  brcr_at     : codepos1;   (* position k of the conditional *)
  brcr_branch : bool;       (* branch b taken *)
}

(* [t_bdhoare_rcond { brcr_at = k; brcr_branch = b }] — decides the
   conditional [i = c[k]] of [phoare [c : P ==> Q] ~ d], with
   [c = hd; i; tl]. Resolves [k] to an index (failing with "invalid split
   index" when it is invalid, then with "the targetted instruction is not a
   conditionnal" when [i] is neither an [if] nor a [while]), then applies

     [EcBdHoareTransform.t_bdhoare_transform] with
       [EcTrRCond.TrRCond { trrc_at = k (resolved); trrc_branch = b }]

   Visible goals, in this order (those of the rule):
     hoare [hd : P ==> e]          (b = true; [!e] when b = false)
     phoare [c' : P ==> Q] ~ d
   with [c'] the decided statement (see [EcTrRCond]). Emits no node of its
   own. *)
val t_bdhoare_rcond : bdhoare_rcond_rule -> backward

(* ==================================================================== *)
(* Elaboration                                                          *)

(* [rcondt k] / [rcondf k] on a [bdHoareS] goal: types the position [k] in
   the goal's memory and applies [t_bdhoare_rcond]. *)
val process_bdhoare_rcond : bool -> pcodepos1 -> backward
