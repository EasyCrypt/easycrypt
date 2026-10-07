(* -------------------------------------------------------------------- *)
open EcMatching.Position

(* ==================================================================== *)
(* Catalogue entry (trusted)                                            *)

type tr_cfold = {
  trcf_at    : nm_codepos;   (* position of the assignment (resolved,
                                possibly nested) *)
  trcf_len   : int option;   (* number n of instructions to scan after it;
                                [None]: up to the end of its block *)
  trcf_eager : bool;         (* eager propagation *)
}

(* [TrCFold { trcf_at = p; trcf_len = n; trcf_eager = eager }] —
   constant folding: propagates the assignment [xs <- es] to local
   variables at position [p] into the (at most [n]) instructions that
   follow it in its block, as long as this is valid, and materializes the
   propagated values afterwards:

     c = C[xs <- es; c1; c2; c3]   ~~>   c' = C[c1'; ys <- fs; c2; c3]

   where [c1] is the longest prefix of the scanned instructions [c1; c2]
   through which the propagation proceeds, [c1'] is [c1] with the
   propagated values substituted (and simplified, without delta), [ys] the
   variables still propagated at the end of [c1] and [fs] their values, and
   [c3] the instructions not scanned. An assignment to a variable read by a
   propagated value stops the propagation, unless [eager], in which case
   that variable is propagated too; calls, loops, conditionals, matches and
   samplings stop it when they write a propagated variable or a variable
   read by a propagated value; abstract statements when they read or write
   one of them, or make calls; [raise] always stops it.

   No obligation. Same memory. Fails with "invalid code position" when [p]
   is not a position of [c], "expecting at least n instructions" when the
   block has fewer than [n + 1] instructions from [p], "cannot find a
   left-value assignment at given position" when the instruction at [p] is
   not an assignment, and "left-values must be made of local variables
   only" when it assigns a global. *)
type EcPlTransform.transform += TrCFold of tr_cfold
