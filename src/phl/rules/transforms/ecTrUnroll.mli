(* -------------------------------------------------------------------- *)
open EcMatching.Position

(* ==================================================================== *)
(* Catalogue entry (trusted)                                            *)

type tr_unroll = {
  trun_at : nm_codepos;   (* position of the loop (resolved, maybe nested) *)
}

(* [TrUnroll { trun_at = p }] — unrolls the first iteration of the loop
   at the (possibly nested) position [p]:

     c = ...; while e do c1; ...   ~~>   c' = ...; if e then c1;
                                                   while e do c1; ...

   No obligation, the memory is unchanged. Fails with "invalid code
   position" when [p] is not an instruction of [c], and with "cannot find
   a while loop at given position" when that instruction is not a
   [while]. *)
type EcPlTransform.transform += TrUnroll of tr_unroll
