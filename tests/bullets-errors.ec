(* Negative tests for strict bullets: each `fail …' phrase is expected
   to error out; the surrounding proof must still finish cleanly. *)
require import AllCore.

pragma +strict_bullets.

(* Reusing a bullet before the previous subgoal is closed. *)
lemma reuse_not_closed (p q : bool) : p => q => p /\ q.
proof.
move=> hp hq; split.
- idtac.
fail - exact hp.
exact hp.
- exact hq.
qed.

(* Using a bullet more times than there are sibling subgoals. The
   `fail' here triggers `NoSubgoalToOpen' (every sibling has already
   been closed). *)
lemma too_many (p q : bool) : p => q => p /\ q.
proof.
move=> hp hq; split.
- exact hp.
- exact hq.
fail - exact hp.
qed.

(* Reuse-before-closing with sibling goals still open. Unlike the
   `too_many' lemma above, here the focused sibling is left open by
   `idtac', so the next `-' must trigger `ReuseBeforeClosing' (not
   `NoSubgoalToOpen'). *)
lemma reuse_with_open (p q r : bool) :
  p => q => r => p /\ q /\ r.
proof.
move=> hp hq hr; do! split.
- exact hp.
- idtac.
fail - exact hr.
exact hq.
exact hr.
qed.

(* Outer bullet reused while an inner bullet level still has open
   subgoals. *)
lemma wrong_skip (p q r s : bool) :
  p => q => r => s => (p /\ q) /\ (r /\ s).
proof.
move=> hp hq hr hs; split.
- split.
  + exact hp.
fail - split.
  + exact hq.
- split.
  + exact hr.
  + exact hs.
qed.
