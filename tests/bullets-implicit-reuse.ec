(* Regression: after an implicit last sibling closes an inner frame,
   the bullet character used inside that frame must be free to reuse
   at the parent level. *)
require import AllCore.

pragma +strict_bullets.

(* Outer split bulleted with `+'; inner split inside the first child
   uses `-'. The first child's last sibling is taken implicitly. Then
   the outer's last sibling is also taken implicitly, where a fresh
   `split' begins a new bullet stack and `+' must again be available. *)
lemma reuse_after_implicit (a b c d : bool) :
  a => b => c => d => (a /\ b) /\ (c /\ d).
proof.
move=> ha hb hc hd; split.
+ split.
  - exact ha.
  exact hb.       (* implicit last sibling of inner `-' frame *)
split.            (* implicit last sibling of outer `+' frame *)
+ exact hc.
exact hd.
qed.

(* Variant: longer outer enumeration; each child uses its own inner
   character and an implicit final sibling. *)
lemma reuse_after_implicit3 (a b c d e f : bool) :
  a => b => c => d => e => f =>
  (a /\ b) /\ (c /\ d) /\ (e /\ f).
proof.
move=> ha hb hc hd he hf; split.
+ split.
  - exact ha.
  exact hb.
split.
+ split.
  - exact hc.
  exact hd.
split.
- exact he.
exact hf.
qed.
