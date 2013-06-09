type t.
pred p: t.

lemma l: forall x1, p x1 => forall x2 x3, p x2 => p x3.
proof.
intros x1 hx1 x2 x3 hx2.
generalize x1 hx1 x2 x3 hx2.
clear hx1 x1.
clear hx2 x2 x3.
admit.
save.