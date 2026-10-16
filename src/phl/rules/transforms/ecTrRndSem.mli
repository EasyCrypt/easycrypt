(* -------------------------------------------------------------------- *)
open EcMatching.Position

(* ==================================================================== *)
(* Catalogue entry (trusted)                                            *)

type tr_rndsem = {
  trrs_at     : nm_codegap1;   (* start k of the suffix (resolved index) *)
  trrs_reduce : bool;          (* sample only the variables of the post *)
}

(* [TrRndSem { trrs_at = k; trrs_reduce = red }] — semantic sampling of a
   straight-line suffix:

     c = c1; c2   (c1 = c[0..k))   ~~>   c' = c1; wr <$ D(c2)

   where [c2] consists of assignments and samplings only and writes no
   global, [wr] are the variables written by [c2] — only those read by the
   judgement's postcondition (the context's [trc_post]) when [red] — and
   [D(c2)] is the distribution of their final values, [c2] read as nested
   [dlet] / [dunit] (see [EcPlRndSem.semrnd]). When [wr] is empty, a fresh
   [unit] variable is added to the memory and sampled instead. No
   obligation. Fails with "semrnd" when [c2] is not of that form. *)
type EcPlTransform.transform += TrRndSem of tr_rndsem
