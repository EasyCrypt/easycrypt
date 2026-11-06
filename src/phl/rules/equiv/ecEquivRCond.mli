(* -------------------------------------------------------------------- *)
open EcParsetree
open EcCoreGoal.FApi
open EcMatching.Position

(* ==================================================================== *)
(* Derived tactics                                                      *)

type equiv_rcond_rule = {
  ercr_side   : side;       (* side of the conditional *)
  ercr_at     : codepos1;   (* position k of the conditional, on that side *)
  ercr_branch : bool;       (* branch b taken *)
}

(* [t_equiv_rcond { ercr_side = `Left; ercr_at = k; ercr_branch = b }] —
   decides the conditional [i = c[k]] of the left program of
   [equiv [c ~ d : P ==> Q]], with [c = hd; i; tl] (symmetrically for
   [`Right]). Resolves [k] to an index (failing with "invalid split index"
   when it is invalid, then with "the targetted instruction is not a
   conditionnal" when [i] is neither an [if] nor a [while]), then applies

     [EcEquivTransform.t_equiv_transform] on that side with
       [EcTrRCond.TrRCond { trrc_at = k (resolved); trrc_branch = b }]

   Visible goals, in this order (those of the rule):
     forall &2, hoare [hd : P ==> e]   (b = true; [!e] when b = false)
     equiv [c' ~ d : P ==> Q]
   with [c'] the decided statement (see [EcTrRCond]). Emits no node of its
   own. *)
val t_equiv_rcond : equiv_rcond_rule -> backward

(* ==================================================================== *)
(* Elaboration                                                          *)

(* [rcondt{i} k] / [rcondf{i} k] on an [equivS] goal: types the position
   [k] in the memory of side [i] and applies [t_equiv_rcond]. *)
val process_equiv_rcond : side -> bool -> pcodepos1 -> backward
