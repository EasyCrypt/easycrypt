(* Multi-character bullets (`--`, `++`, etc.) for deeper nesting. *)
require import AllCore.

pragma +strict_bullets.

(* `--` opens a level distinct from `-`. *)
lemma deep2 (a b c d : bool) :
  a => b => c => d => (a /\ b) /\ (c /\ d).
proof.
move=> ha hb hc hd; split.
- split.
  -- exact ha.
  -- exact hb.
- split.
  -- exact hc.
  -- exact hd.
qed.

(* `+++` and `***` also work; characters and lengths can be combined. *)
lemma deep3 (a b c d e f g h : bool) :
  a => b => c => d => e => f => g => h =>
  ((a /\ b) /\ (c /\ d)) /\ ((e /\ f) /\ (g /\ h)).
proof.
move=> ha hb hc hd he hf hg hh; split.
- split.
  + split.
    * exact ha.
    * exact hb.
  + split.
    * exact hc.
    * exact hd.
- split.
  + split.
    * exact he.
    * exact hf.
  + split.
    * exact hg.
    * exact hh.
qed.
