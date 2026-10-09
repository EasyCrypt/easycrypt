(* -------------------------------------------------------------------- *)
open EcSymbols
open EcMatching.Position

(* ==================================================================== *)
(* Catalogue entry (trusted)                                            *)

type tr_alias = {
  tral_at   : nm_codepos;   (* position of the instruction (resolved,
                               possibly nested) *)
  tral_name : symbol;       (* name of the alias *)
}

(* [TrAlias { tral_at = p; tral_name = x }] — names the value computed by
   the instruction at position [p] (an assignment, a sampling or a call
   with a left-value), through a fresh program variable [x'] (named after
   [x], added to the memory):

     c = C[lv <- e]          ~~>   c' = C[x' <- e; lv <- x']
     c = C[lv <$ d]          ~~>   c' = C[x' <$ d; lv <- x']
     c = C[lv <@ f(args)]    ~~>   c' = C[x' <@ f(args); lv <- x']

   No obligation. Fails with "invalid code position" when [p] is not the
   position of an instruction of [c], and "cannot create an alias for that
   kind of instruction" otherwise. *)
type EcPlTransform.transform += TrAlias of tr_alias
