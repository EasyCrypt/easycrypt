(* -------------------------------------------------------------------- *)
open EcParsetree
open EcCoreGoal.FApi
open EcMatching.Position

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

type equiv_rndsem_rule = {
  ersr_side   : side;       (* rewritten side *)
  ersr_at     : codegap1;   (* start k of the suffix, on that side *)
  ersr_reduce : bool;       (* sample only the variables of the post *)
}

(* [t_equiv_rndsem { ersr_side = `Left; ersr_at = k; ersr_reduce = red }]
   — semantic sampling of a straight-line suffix of one side:

       equiv [c1; wr <$ D(c2) ~ c' : P ==> Q]
     ------------------------------------------  c = c1; c2   (c1 = c[0..k))
               equiv [c ~ c' : P ==> Q]

   (symmetrically for [`Right]), where [c2] consists of assignments and
   samplings only and writes no global, [wr] are the variables written by
   [c2] — only those occurring in [Q] (on that side) when [red] — and
   [D(c2)] is the distribution of their final values (see
   [EcPlRndSem.semrnd]). When [wr] is empty, a fresh [unit] variable is
   added to the memory of that side and sampled instead.

   As for hoare, the suffix is rewritten in place, keeping the prefix
   [c1]: a program transformation, not expressible through [seq].

   Node: [REquivRndSem { ersn_side; ersn_at = k (resolved index);
                         ersn_reduce = red }].
   Checker: "equiv-rndsem". *)
val t_equiv_rndsem : equiv_rndsem_rule -> backward

(* ==================================================================== *)
(* Elaboration                                                          *)

(* [rndsem[*]{i} k] on an [equivS] goal (the star sets [reduce]): side
   required. Applies [t_equiv_rndsem]. *)
val process_equiv_rndsem : reduce:bool -> oside -> pcodegap1 -> backward
