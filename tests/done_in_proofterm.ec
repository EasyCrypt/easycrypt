require import AllCore.

op p : int -> int -> bool.

axiom A (x y : int) : x <= y => x-1 <= y => x-2 <= y => p x y.

lemma L x : p x x.
proof. by have := A x x //# // /#; [smt() | apply]. qed.


