(* -------------------------------------------------------------------- *)
open EcParsetree
open EcCoreGoal.FApi
open EcMatching.Position

(* ==================================================================== *)
(* Derived tactics                                                      *)

type bdhoare_rndsem_rule = {
  brsr_at     : codegap1;   (* start k of the suffix *)
  brsr_reduce : bool;       (* sample only the variables of the post *)
}

(* [t_bdhoare_rndsem { brsr_at = k; brsr_reduce = red }] — semantic
   sampling of the straight-line suffix [c2] of
   [phoare [c1; c2 : P ==> Q] ~ d], with [c1 = c[0..k)]. Resolves [k] to
   an index, then applies

     [EcBdHoareTransform.t_bdhoare_transform] with
       [EcTrRndSem.TrRndSem { trrs_at = k (resolved); trrs_reduce = red }]

   (no obligation), giving  phoare [c1; wr <$ D(c2) : P ==> Q] ~ d
   (failing with "semrnd" when [c2] is not straight-line or writes a
   global).

   Visible goal: the transformed judgement. Emits no node of its own. *)
val t_bdhoare_rndsem : bdhoare_rndsem_rule -> backward

(* ==================================================================== *)
(* Elaboration                                                          *)

(* [rndsem[*] k] on a [bdHoareS] goal (the star sets [reduce]): no side.
   Applies [t_bdhoare_rndsem]. *)
val process_bdhoare_rndsem : reduce:bool -> oside -> pcodegap1 -> backward
