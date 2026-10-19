(* -------------------------------------------------------------------- *)
open EcMatching.Position

(* ==================================================================== *)
(* Catalogue entry (trusted)                                            *)

type tr_kill = {
  trk_at  : nm_codepos;   (* position of the first killed instruction
                             (resolved, possibly nested) *)
  trk_len : int option;   (* number n of killed instructions; [None]: up
                             to the end of their block *)
}

(* [TrKill { trk_at = p; trk_len = n }] — removes the [n] instructions
   [ks] at position [p] (in the block of [p], possibly nested):

     c = C[ks; tl]   ~~>   c' = C[tl]

   provided that no variable written by [ks] is read by the code that may
   run after it ([tl], the instructions following each enclosing
   instruction, and, for each enclosing while loop, its guard and its
   whole body, as the next iterations run them again: [EcPV.zpr_pv `Read
   `After]), nor by the postcondition (the context's [trc_post], for
   hoare including the exceptional postconditions). One obligation:
   [OLossless ks], in the memory of [c]. Same memory. Fails with "invalid
   code position" when [p] is not a position of [c], "cannot find n
   consecutive instructions at given position" when the block has fewer
   than [n] instructions from [p], and "code writes variables (x) used by
   the code that may run after it / the post-condition" when the
   independence condition does not hold. *)
type EcPlTransform.transform += TrKill of tr_kill
