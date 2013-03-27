require import Int.

lemma l: forall x1,
  let x2 = x1 + x1 in
  let x3 = x2 + x2 in
  x3 = x1 + x1 + x1 + x1
proof.
intros x1 x2 x3. (* FIXME: printing of let hyp *)
trivial.
save.