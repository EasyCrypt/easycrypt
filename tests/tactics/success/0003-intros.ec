type t.
pred p: t.

lemma l: forall x1, p x1 => forall x2 x3, p x2 => p x3.
proof -strict.
intros x1 hx1 x2.
intros x3 hx2.
admit.
qed.

op test = (fun x, let y = 3 in x = y) 3.

lemma intro_after_delta: test.
proof -strict.
intros x.
admit.
qed.