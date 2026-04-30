(* -------------------------------------------------------------------- *)
require import AllCore.

(* -------------------------------------------------------------------- *)
lemma L1 (c d x : int) : x + (x + c) = x.
proof.
rewrite (_ : x + _ = d).
- suff: x + (x + c) = d by exact. admit.
- suff: d = x by exact. admit.
qed.

(* -------------------------------------------------------------------- *)
lemma L2 (c d x : int) : x + (x + c) = x.
proof.
rewrite [_ + c](_ : x + _ = d).
- suff: x + c = d by exact. admit.
- suff: x + d = x by exact. admit.
qed.

(* -------------------------------------------------------------------- *)
lemma L3 (c d x : int) : x + (x + c) = x.
proof.
rewrite [_ + c](_ : _ + c = d).
- suff: x + c = d by exact. admit.
- suff: x + d = x by exact. admit.
qed.

(* -------------------------------------------------------------------- *)
(* Contextual pattern: [y in x + y] targets the second argument of the
   outer addition, leaving the first x untouched. *)
lemma L4 (c d x : int) : x + (x + c) = x.
proof.
rewrite [y in x + y](_ : y = d).
- suff: x + c = d by exact. admit.
- suff: x + d = x by exact. admit.
qed.

(* -------------------------------------------------------------------- *)
(* Contextual pattern in a deeper nesting: [y in y + c] picks the
   inner (x + c) subterm of ((x + c) + c). *)
lemma L5 (c d x : int) : (x + c) + c = x.
proof.
rewrite [y in y + c](_ : y = d).
- suff: x + c = d by exact. admit.
- suff: d + c = x by exact. admit.
qed.

(* -------------------------------------------------------------------- *)
(* Contextual pattern with a more complex context expression. *)
lemma L6 (a b c x : int) : (a + b) * (a + c) = x.
proof.
rewrite [y in y * (a + c)](_ : y = c).
- suff: a + b = c by exact. admit.
- suff: c * (a + c) = x by exact. admit.
qed.

(* -------------------------------------------------------------------- *)
(* Contextual pattern with a definition: ensure no unfolding occurs
   during pattern search, which would make position computation wrong. *)
op f (x : int) = x + 1.

lemma L7 (a b : int) : f a + f b = a.
proof.
rewrite [y in f y + _](_ : y = b).
- suff: a = b by exact. admit.
- suff: f b + f b = a by exact. admit.
qed.

(* -------------------------------------------------------------------- *)
(* Same but the contextual pattern involves the defined operator. *)
lemma L7b (a b c : int) : f a + f b = c.
proof.
rewrite [y in y + f b](_ : y = a).
- suff: f a = a by exact. admit.
- suff: a + f b = c by exact. admit.
qed.

(* -------------------------------------------------------------------- *)
(* Contextual pattern where the pattern could match via unfolding of f.
   The pattern [y in y + 1] should NOT match f a (which unfolds to a + 1),
   because that would make position computation wrong. *)
lemma L7c (a b : int) : f a + f b = a.
proof.
fail rewrite [y in y + 1](_ : y = b).
abort.

(* -------------------------------------------------------------------- *)
(* Reverse: pattern mentions f but goal has the unfolded form.
   [y in f y] should NOT match in (a + 1) + (b + 1) via folding. *)
lemma L7d (a b : int) : (a + 1) + (b + 1) = a.
proof.
fail rewrite [y in f y](_ : y = b).
abort.

(* -------------------------------------------------------------------- *)
(* Inner unfolding: the pattern [y in y + (x + 1)] could match
   y + f x via inner unfolding of f. This risks making the position
   computation wrong because prw would be the unfolded form while the
   goal still has f x. *)
op g (x y : int) = x + y.

lemma L7e (a b x : int) : g a (f x) + g b (f x) = a.
proof.
rewrite [y in g y (f x)](_ : _ = b).
- suff: a = b by exact. admit.
- suff: g b (f x) + g b (f x) = a by exact. admit.
qed.

(* -------------------------------------------------------------------- *)
(* Pattern has unfolded form of f in an inner position.
   Conversion is disabled for contextual pattern search, so this
   must fail even though y is not part of the unfolded subterm. *)
lemma L7f (a b x : int) : g a (f x) + g b (f x) = a.
proof.
fail rewrite [y in g y (x + 1)](_ : y = b).
abort.

(* -------------------------------------------------------------------- *)
(* Dangerous case: y IS part of the unfolded subterm. The pattern
   [y in (3 + y + 1) + f b] could match foo a via inner unfolding,
   but that would make position computation wrong. Must be rejected. *)
op h (x : int) = 3 + x + 1.

lemma L7g (a b : int) : h a + f b = a.
proof.
fail rewrite [y in (3 + y + 1) + f b](_ : y = b).
abort.

(* -------------------------------------------------------------------- *)
(* Error: context variable does not appear in the r-pattern — should fail. *)
lemma L8_fail (c d x : int) : x + (x + c) = x.
proof.
fail rewrite [y in x + x](_ : x + c = d).
abort.

(* -------------------------------------------------------------------- *)
(* Error: context variable appears twice — non-linear, should fail. *)
lemma L9_fail (c d x : int) : x + (x + c) = x.
proof.
fail rewrite [y in y + y](_ : x = d).
abort.

(* -------------------------------------------------------------------- *)
(* Error: rewrite rule LHS does not match the selected subterm. *)
lemma L10_fail (c d x : int) : x + (x + c) = x.
proof.
fail rewrite [y in x + y](_ : x = d).
abort.
