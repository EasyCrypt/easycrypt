op iff (x y:bool): bool = x <=> y.
op or  (x y:bool): bool = x \/ y.

lemma l: forall b, iff (or true b) true
proof.
intros b.
delta.
beta.
trivial.
save.