(* Under +strict_bullets, a phrase that produces multiple subgoals
   must be followed by a bullet — strict mode cannot be bypassed by
   simply omitting bullets entirely. Each `fail …' phrase is expected
   to error out; the surrounding proof must still finish cleanly. *)
require import AllCore.

pragma +strict_bullets.

(* Naked split at top level: an unbulleted phrase that follows is
   ambiguous and must be rejected. *)
lemma naked_top (p q : bool) : p => q => p /\ q.
proof.
move=> hp hq; split.
fail exact hp.
- exact hp.
- exact hq.
qed.

(* Naked split nested inside a `+' frame: same rule applies at the
   inner level. *)
lemma naked_nested (a b c d : bool) :
  a => b => c => d => (a /\ b) /\ (c /\ d).
proof.
move=> ha hb hc hd; split.
+ split.
  fail exact ha.
  - exact ha.
  exact hb.
+ split.
  - exact hc.
  exact hd.
qed.
