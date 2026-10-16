(* -------------------------------------------------------------------- *)
open EcParsetree
open EcCoreGoal.FApi
open EcMatching.Position

(* ==================================================================== *)
(* Derived tactics                                                      *)

type hoare_rcond_rule = {
  hrcr_at     : codepos1;   (* position k of the conditional *)
  hrcr_branch : bool;       (* branch b taken *)
}

(* [t_hoare_rcond { hrcr_at = k; hrcr_branch = b }] — decides the
   conditional [i = c[k]] of [hoare [c : P ==> Q | E]], with
   [c = hd; i; tl]. Resolves [k] to an index (failing with "invalid split
   index" when it is invalid, then with "the targetted instruction is not a
   conditionnal" when [i] is neither an [if] nor a [while]), then applies

     [EcHoareTransform.t_hoare_transform] with
       [EcTrRCond.TrRCond { trrc_at = k (resolved); trrc_branch = b }]

   Visible goals, in this order (those of the rule):
     hoare [hd : P ==> e | E]      (b = true; [!e] when b = false)
     hoare [c' : P ==> Q | E]
   with [c'] the decided statement (see [EcTrRCond]). Emits no node of its
   own. *)
val t_hoare_rcond : hoare_rcond_rule -> backward

(* ==================================================================== *)
(* Elaboration                                                          *)

(* [rcondt k] / [rcondf k] on a [hoareS] goal: types the position [k] in
   the goal's memory and applies [t_hoare_rcond]. *)
val process_hoare_rcond : bool -> pcodepos1 -> backward
