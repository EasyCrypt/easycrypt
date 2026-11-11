(* Bullets as focusing operators: basic usage. *)
require import AllCore.

pragma +strict_bullets.

(* Two subgoals, two bullets. *)
lemma split2 (p q : bool) : p => q => p /\ q.
proof.
move=> hp hq; split.
- exact hp.
- exact hq.
qed.

(* Three subgoals at the same depth. *)
lemma split3 (p q r : bool) : p => q => r => p /\ q /\ r.
proof.
move=> hp hq hr; do! split.
- exact hp.
- exact hq.
- exact hr.
qed.

(* Nested: outer `-`, inner `+`. *)
lemma nested (p q r s : bool) :
  p => q => r => s => (p /\ q) /\ (r /\ s).
proof.
move=> hp hq hr hs; split.
- split.
  + exact hp.
  + exact hq.
- split.
  + exact hr.
  + exact hs.
qed.

(* Three-deep nesting using `-`, `+`, `*`. *)
lemma deep (a b c d : bool) :
  a => b => c => d => ((a /\ b) /\ c) /\ d.
proof.
move=> ha hb hc hd; split.
- split.
  + split.
    * exact ha.
    * exact hb.
  + exact hc.
- exact hd.
qed.

(* No bullet between sub-tactics on the same goal works fine: tactics
   chained with `;' inside one phrase don't trigger new bullet checks. *)
lemma chained (p q : bool) : p => q => p /\ q.
proof.
move=> hp hq; split.
- exact hp.
- exact hq.
qed.
