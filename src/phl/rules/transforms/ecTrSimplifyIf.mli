(* -------------------------------------------------------------------- *)
open EcMatching.Position

(* ==================================================================== *)
(* Catalogue entry (trusted)                                            *)

type tr_simplify_if = {
  trsi_at : nm_codepos;   (* position of the conditional (resolved,
                             possibly nested) *)
}

(* [TrSimplifyIf { trsi_at = p }] — turns the conditional at position [p],
   whose branches are sequences of assignments, into a single assignment:

     c = C[if e then c1 else c2]   ~~>   c' = C[xs <- es]

   where [xs] are the (local) variables written by [c1] or [c2] and [es]
   computes their final values: [c1] and [c2] are read as nested [let]s
   (on fresh local binders) over [if e then xs1 else xs2], [xsi] being the
   values of [xs] at the end of [ci]. When [xs] is empty, the conditional
   is removed. No obligation. Same memory. Fails with "invalid code
   position" when [p] is not the position of an instruction of [c], "the
   given position does not correspond to an if instruction", "the then
   (resp. else) branch contains intruction that are not assignments", and
   "the branches modify global variables". *)
type EcPlTransform.transform += TrSimplifyIf of tr_simplify_if
