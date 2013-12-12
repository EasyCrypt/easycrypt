type t.
pred p: t.

axiom l_admit: forall x, p x.

lemma l: forall x, p x.
proof -strict.
assumption l_admit.
qed.