module type I = {
}.

lemma L : forall (M <: I), true.
proof -strict.
 intros M;smt.
qed.
