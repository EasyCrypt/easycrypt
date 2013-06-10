op iff (x y : bool) : bool = x <=> y.
op and (x y : bool) : bool = x /\ y.
op or  (x y : bool) : bool = x \/ y.

lemma l_simplify_delta : iff (and true true) true.
proof.
  delta beta logic.
  trivial.
save.

lemma l_simplify_logic : iff (and true false) false /\ (true = true).
proof.
  simplify and or iff.
  trivial.
save.

lemma l_normalize : iff (and true false) false /\ (true = true).
proof.
  simplify delta.
  trivial.
save.

lemma l_change : iff (and true false) false /\ (true = true).
proof.
  change true.
  trivial.
save.