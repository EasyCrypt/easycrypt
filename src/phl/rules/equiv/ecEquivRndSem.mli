(* -------------------------------------------------------------------- *)
open EcParsetree
open EcCoreGoal.FApi
open EcMatching.Position

(* ==================================================================== *)
(* Derived tactics                                                      *)

type equiv_rndsem_rule = {
  ersr_side   : side;       (* rewritten side *)
  ersr_at     : codegap1;   (* start k of the suffix, on that side *)
  ersr_reduce : bool;       (* sample only the variables of the post *)
}

(* [t_equiv_rndsem { ersr_side = `Left; ersr_at = k; ersr_reduce = red }]
   — semantic sampling of the straight-line suffix [c2] of the left program
   of [equiv [c1; c2 ~ c' : P ==> Q]], with [c1 = c[0..k)] (symmetrically
   for [`Right]). Resolves [k] to an index, then applies

     [EcEquivTransform.t_equiv_transform] on that side with
       [EcTrRndSem.TrRndSem { trrs_at = k (resolved); trrs_reduce = red }]

   (no obligation), giving  equiv [c1; wr <$ D(c2) ~ c' : P ==> Q]
   (failing with "semrnd" when [c2] is not straight-line or writes a
   global).

   Visible goal: the transformed judgement. Emits no node of its own. *)
val t_equiv_rndsem : equiv_rndsem_rule -> backward

(* ==================================================================== *)
(* Elaboration                                                          *)

(* [rndsem[*]{i} k] on an [equivS] goal (the star sets [reduce]): side
   required. Applies [t_equiv_rndsem]. *)
val process_equiv_rndsem : reduce:bool -> oside -> pcodegap1 -> backward
