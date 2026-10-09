(* -------------------------------------------------------------------- *)
open EcSymbols
open EcAst
open EcMatching
open EcMatching.Position

(* ==================================================================== *)
(* Catalogue entry (trusted)                                            *)

type tr_set_match = {
  trsm_at   : nm_codepos;   (* position of the instruction (resolved,
                               possibly nested) *)
  trsm_name : symbol;       (* name of the new variable *)
  trsm_sub  : ss_inv;       (* the named subterm [t] (read in the memory
                               of [c]) *)
  trsm_occ  : ptnpos;       (* its occurrences in the expression of the
                               instruction *)
}

(* [TrSetMatch { trsm_at = p; trsm_name = x; trsm_sub = t; trsm_occ = o }]
   — names the subterm [t] of the expression [e] of the instruction [i] at
   position [p] (an assignment, a sampling, a conditional or a match),
   through a fresh program variable [x'] (named after [x], added to the
   memory):

     c = C[i(e)]   ~~>   c' = C[x' <- t; i(e[o := x'])]

   where every occurrence selected by [o] in [e] must be alpha-equivalent
   to [t]. No obligation. Fails with "invalid code position" when [p] is
   not the position of an instruction of [c], "targetted instruction
   should contain an expression" or "while loops not supported" when [i]
   is not of the expected kind, and "cannot find an occurrence of the
   pattern" when [o] does not select occurrences of [t] in [e]. *)
type EcPlTransform.transform += TrSetMatch of tr_set_match
