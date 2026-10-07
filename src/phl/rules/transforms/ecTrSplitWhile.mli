(* -------------------------------------------------------------------- *)
open EcTypes
open EcMatching.Position

(* ==================================================================== *)
(* Catalogue entry (trusted)                                            *)

type tr_splitwhile = {
  trsw_at   : nm_codepos;   (* position of the loop (resolved, maybe nested) *)
  trsw_cond : expr;         (* the additional condition b (typed, bool) *)
}

(* [TrSplitWhile { trsw_at = p; trsw_cond = b }] — splits the loop at the
   (possibly nested) position [p] into the iterations where [b] also
   holds, then the remaining ones:

     c = ...; while e do c1; ...   ~~>   c' = ...; while (e /\ b) do c1;
                                                   while e do c1; ...

   No obligation, the memory is unchanged. Fails with "invalid code
   position" when [p] is not an instruction of [c], and with "cannot find
   a while loop at given position" when that instruction is not a
   [while]. *)
type EcPlTransform.transform += TrSplitWhile of tr_splitwhile
