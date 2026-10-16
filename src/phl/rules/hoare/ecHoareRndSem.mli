(* -------------------------------------------------------------------- *)
open EcParsetree
open EcCoreGoal.FApi
open EcMatching.Position

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

type hoare_rndsem_rule = {
  hrsr_at     : codegap1;   (* start k of the suffix *)
  hrsr_reduce : bool;       (* sample only the variables of the post *)
}

(* [t_hoare_rndsem { hrsr_at = k; hrsr_reduce = red }] — semantic sampling
   of a straight-line suffix:

       hoare [c1; wr <$ D(c2) : P ==> Q]
     -------------------------------------  c = c1; c2   (c1 = c[0..k))
             hoare [c : P ==> Q]

   where [c2] consists of assignments and samplings only and writes no
   global, [wr] are the variables written by [c2] — only those occurring
   in [Q] when [red] — and [D(c2)] is the distribution of their final
   values, [c2] read as nested [dlet] / [dunit] (see [EcPlRndSem.semrnd]).
   When [wr] is empty, a fresh [unit] variable is added to the memory and
   sampled instead. Side condition: no exceptional postcondition.

   This rule rewrites the suffix [c2] in place, keeping the prefix [c1]: it
   is a program transformation (replacing [c2] by an equivalent sampling),
   which is not expressible through [seq] without an intermediate assertion
   after [c1] that the tactic does not have.

   Node: [RHoareRndSem { hrsn_at = k (resolved index); hrsn_reduce = red }].
   Checker: "hoare-rndsem". *)
val t_hoare_rndsem : hoare_rndsem_rule -> backward

(* ==================================================================== *)
(* Elaboration                                                          *)

(* [rndsem[*] k] on a [hoareS] goal (the star sets [reduce]): no side.
   Applies [t_hoare_rndsem]. *)
val process_hoare_rndsem : reduce:bool -> oside -> pcodegap1 -> backward
