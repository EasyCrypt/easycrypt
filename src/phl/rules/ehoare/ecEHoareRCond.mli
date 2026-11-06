(* -------------------------------------------------------------------- *)
open EcParsetree
open EcCoreGoal.FApi
open EcMatching.Position

(* ==================================================================== *)
(* Derived tactics                                                      *)

type ehoare_rcond_rule = {
  ehrcr_at     : codepos1;   (* position k of the conditional *)
  ehrcr_branch : bool;       (* branch b taken *)
}

(* [t_ehoare_rcond { ehrcr_at = k; ehrcr_branch = b }] — decides the
   conditional [i = c[k]] of [ehoare [c : P `|` f ==> Q]], with
   [c = hd; i; tl]. Resolves [k] to an index (failing with "invalid split
   index" when it is invalid, then with "the targetted instruction is not a
   conditionnal" when [i] is neither an [if] nor a [while]), then applies

     [EcEHoareTransform.t_ehoare_transform] with
       [EcTrRCond.TrRCond { trrc_at = k (resolved); trrc_branch = b }]

   (failing with "the pre should have the form \"_ `|` _\"" otherwise).

   Visible goals, in this order (those of the rule):
     hoare [hd : P ==> e]          (b = true; [!e] when b = false)
     ehoare [c' : P `|` f ==> Q]
   with [c'] the decided statement (see [EcTrRCond]). Emits no node of its
   own. *)
val t_ehoare_rcond : ehoare_rcond_rule -> backward

(* ==================================================================== *)
(* Elaboration                                                          *)

(* [rcondt k] / [rcondf k] on an [eHoareS] goal: types the position [k] in
   the goal's memory and applies [t_ehoare_rcond]. *)
val process_ehoare_rcond : bool -> pcodepos1 -> backward
