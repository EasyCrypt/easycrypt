(* -------------------------------------------------------------------- *)
open EcParsetree
open EcCoreGoal.FApi
open EcMatching.Position

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

type bdhoare_rndsem_rule = {
  brsr_at     : codegap1;   (* start k of the suffix *)
  brsr_reduce : bool;       (* sample only the variables of the post *)
}

(* [t_bdhoare_rndsem { brsr_at = k; brsr_reduce = red }] — semantic
   sampling of a straight-line suffix, with [~] the goal's comparison:

       phoare [c1; wr <$ D(c2) : P ==> Q] ~ d
     ------------------------------------------  c = c1; c2   (c1 = c[0..k))
               phoare [c : P ==> Q] ~ d

   where [c2] consists of assignments and samplings only and writes no
   global, [wr] are the variables written by [c2] — only those occurring
   in [Q] when [red] — and [D(c2)] is the distribution of their final
   values (see [EcPlRndSem.semrnd]). When [wr] is empty, a fresh [unit]
   variable is added to the memory and sampled instead.

   As for hoare, the suffix is rewritten in place, keeping the prefix
   [c1]: a program transformation, not expressible through [seq].

   Node: [RBdHoareRndSem { brsn_at = k (resolved index); brsn_reduce = red }].
   Checker: "bdhoare-rndsem". *)
val t_bdhoare_rndsem : bdhoare_rndsem_rule -> backward

(* ==================================================================== *)
(* Elaboration                                                          *)

(* [rndsem[*] k] on a [bdHoareS] goal (the star sets [reduce]): no side.
   Applies [t_bdhoare_rndsem]. *)
val process_bdhoare_rndsem : reduce:bool -> oside -> pcodegap1 -> backward
