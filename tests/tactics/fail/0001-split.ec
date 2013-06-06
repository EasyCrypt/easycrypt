require import Logic.

lemma foo2 : forall (x1:'a1) (x2:'a1),
x1 = x2
proof.
  intros x1 x2.
  split.
