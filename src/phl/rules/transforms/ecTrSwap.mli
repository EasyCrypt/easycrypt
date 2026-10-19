(* -------------------------------------------------------------------- *)
open EcMatching.Position

(* ==================================================================== *)
(* Catalogue entry (trusted)                                            *)

type tr_swap = {
  trsw_range  : nm_codegap_range;   (* block [p : [s..f)] to move (resolved) *)
  trsw_target : nm_codegap1;        (* its destination gap t (resolved) *)
}

(* [TrSwap { trsw_range = (p, (s, f)); trsw_target = t }] — moves the
   block [b = d[s..f)] of the block [d] at the (possibly nested) path [p]
   of [c] (the body of a [while], a branch of an [if] or of a [match]) to
   the gap [t] of [d], outside of [b] ([t <= s] or [f <= t]); the rest of
   [c] is unchanged:

     d = hd; d1; b; tl   ~~>   d' = hd; b; d1; tl     (t <= s, d1 = d[t..s))
     d = hd; b; d2; tl   ~~>   d' = hd; d2; b; tl     (f <= t, d2 = d[f..t))

   Side conditions: neither [b] nor [d1] / [d2] contains a [raise]
   (otherwise fails with "cannot swap blocks that contain exceptions");
   when the judgement observes exceptions (the context's [trc_exn]),
   neither may raise through a procedure call
   ([EcLowPhlGoal.s_may_raise]; otherwise fails with "cannot swap blocks
   that may raise an exception (through a procedure call) when the
   postcondition constrains exceptions"); and the two exchanged statements are independent: the first one reads
   nothing the second one writes, they write nothing in common, and the
   first one writes nothing the second one reads (checked in this order,
   failing with "the two statements are not independent, the first
   statement reads / writes X which is written / read by the second").
   Fails with "invalid range for swap" / "invalid offset for swap" when
   the positions are not valid for [c]. No obligation, the memory is
   unchanged. *)
type EcPlTransform.transform += TrSwap of tr_swap
