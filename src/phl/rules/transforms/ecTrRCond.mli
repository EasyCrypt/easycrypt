(* -------------------------------------------------------------------- *)
open EcMatching.Position

(* ==================================================================== *)
(* Catalogue entry (trusted)                                            *)

type tr_rcond = {
  trrc_at     : nm_codepos1;   (* position k of the conditional (resolved) *)
  trrc_branch : bool;          (* branch b taken *)
}

(* [TrRCond { trrc_at = k; trrc_branch = b }] — decides the conditional
   [i = c[k]] in favour of the branch [b], with [c = hd; i; tl] and
   [hd = c[0..k)]:

     c = hd; if e then c1 else c2; tl   ~~>   c' = hd; c1; tl     (b = true)
                                              c' = hd; c2; tl     (b = false)
     c = hd; while e do c1; tl          ~~>   c' = hd; c1; while e do c1; tl
                                                                  (b = true)
                                              c' = hd; tl         (b = false)

   One obligation: [OPrefixPost (hd, e)] (b = true), [OPrefixPost (hd, !e)]
   (b = false), [e] read in the memory of [c]. Same memory. Fails with "the
   targetted instruction is not a conditionnal" when [i] is neither an [if]
   nor a [while] (see [EcPlRCond.rcond_select]). *)
type EcPlTransform.transform += TrRCond of tr_rcond
