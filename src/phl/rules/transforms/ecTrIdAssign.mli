(* -------------------------------------------------------------------- *)
open EcTypes
open EcMatching.Position

(* ==================================================================== *)
(* Catalogue entry (trusted)                                            *)

type tr_idassign = {
  tria_at : nm_codepos;          (* insertion position (resolved, possibly
                                    nested; may be the end of its block) *)
  tria_pv : prog_var * ty;       (* the program variable [x], typed *)
}

(* [TrIdAssign { tria_at = p; tria_pv = x : t }] — inserts, at position
   [p], the identity assignment of [x]:

     c = C[tl]   ~~>   c' = C[x <- x; tl]

   No obligation, same memory. Side condition: when [x] is a local
   variable, it is bound in the memory, with type [t]. Fails with
   "invalid code position" when [p] is not a position of [c], and
   "invalid program variable" when the side condition does not hold. *)
type EcPlTransform.transform += TrIdAssign of tr_idassign
