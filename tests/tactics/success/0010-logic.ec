op iff (x y:bool): bool = x <=> y.
op and (x y:bool): bool = x /\ y.

lemma l: iff (and true false) false /\ (true = true).
proof.
delta.
beta.
logic.
smt.
save.
