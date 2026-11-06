(* -------------------------------------------------------------------- *)
open EcParsetree
open EcCoreGoal.FApi
open EcMatching.Position

(* ==================================================================== *)
(* Derived tactics                                                      *)

type hoare_rndsem_rule = {
  hrsr_at     : codegap1;   (* start k of the suffix *)
  hrsr_reduce : bool;       (* sample only the variables of the post *)
}

(* [t_hoare_rndsem { hrsr_at = k; hrsr_reduce = red }] — semantic sampling
   of the straight-line suffix [c2] of [hoare [c1; c2 : P ==> Q]], with
   [c1 = c[0..k)]. Resolves [k] to an index, fails with "exceptions are not
   supported" when the goal has an exceptional postcondition, then applies

     [EcHoareTransform.t_hoare_transform] with
       [EcTrRndSem.TrRndSem { trrs_at = k (resolved); trrs_reduce = red }]

   (no obligation), giving  hoare [c1; wr <$ D(c2) : P ==> Q]  (failing
   with "semrnd" when [c2] is not straight-line or writes a global).

   Visible goal: the transformed judgement. Emits no node of its own. *)
val t_hoare_rndsem : hoare_rndsem_rule -> backward

(* ==================================================================== *)
(* Elaboration                                                          *)

(* [rndsem[*] k] on a [hoareS] goal (the star sets [reduce]): no side.
   Applies [t_hoare_rndsem]. *)
val process_hoare_rndsem : reduce:bool -> oside -> pcodegap1 -> backward
