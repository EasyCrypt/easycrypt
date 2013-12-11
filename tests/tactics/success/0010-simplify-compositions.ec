op iff (x y : bool) : bool = x <=> y.
op and (x y : bool) : bool = x /\ y.
op or  (x y : bool) : bool = x \/ y.

lemma l_simplify_delta : iff (and true true) true.
proof.
  delta beta logic.
  smt.
qed.

lemma l_simplify_logic : iff (and true false) false /\ (true = true).
proof.
  simplify and or iff.
  smt.
qed.

lemma l_normalize : iff (and true false) false /\ (true = true).
proof.
  simplify delta.
  smt.
qed.

lemma l_change : iff (and true false) false /\ (true = true).
proof.
  change true.
  smt.
qed.