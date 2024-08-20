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
