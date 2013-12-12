(* -------------------------------------------------------------------- *)
type t.

pred p: t.

lemma L: forall x1, p x1 => forall x2 x3, p x2 => p x3.
proof -strict.
intros x1 hx1 x2 x3 hx2.
generalize (x1) hx1 (x2) x3 hx2.
clear x1 x2.
admit.
qed.
