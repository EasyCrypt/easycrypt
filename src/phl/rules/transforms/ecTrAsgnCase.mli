(* -------------------------------------------------------------------- *)
open EcMatching.Position

(* ==================================================================== *)
(* Catalogue entry (trusted)                                            *)

type tr_asgn_case = {
  trac_at : nm_codepos;   (* position of the assignment (resolved,
                             possibly nested) *)
}

(* [TrAsgnCase { trac_at = p }] — splits the (tuple) assignment at
   position [p] into one assignment per variable:

     c = C[(x_1, ..., x_n) <- e]   ~~>   c' = C[x_1 <- e_1; ...; x_n <- e_n]

   where [e_i] is the [i]-th component of [e] when [e] is a syntactic
   tuple, its [i]-th projection otherwise (the assignment is unchanged
   when it assigns a single variable). Side condition: [x_1 ... x_(n-1)]
   are not read by [e]. No obligation. Same memory. Fails with "invalid
   code position" when [p] is not the position of an instruction of [c],
   "the code position should target an assignment" when it is not an
   assignment, and "the assigned variables are read by the assigned
   expression" when the side condition does not hold. *)
type EcPlTransform.transform += TrAsgnCase of tr_asgn_case
