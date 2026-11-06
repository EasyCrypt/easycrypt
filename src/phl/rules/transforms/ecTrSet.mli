(* -------------------------------------------------------------------- *)
open EcSymbols
open EcTypes
open EcMatching.Position

(* ==================================================================== *)
(* Catalogue entry (trusted)                                            *)

type tr_set = {
  trs_at   : nm_codepos;   (* insertion position (resolved, possibly
                              nested; may be the end of its block) *)
  trs_name : symbol;       (* name of the new variable *)
  trs_e    : expr;         (* its value, typed in the memory of [c] *)
}

(* [TrSet { trs_at = p; trs_name = x; trs_e = e }] — inserts, at position
   [p], the assignment of [e] to a fresh program variable [x'] (named
   after [x], added to the memory):

     c = C[tl]   ~~>   c' = C[x' <- e; tl]

   No obligation. Fails with "invalid code position" when [p] is not a
   position of [c]. *)
type EcPlTransform.transform += TrSet of tr_set
