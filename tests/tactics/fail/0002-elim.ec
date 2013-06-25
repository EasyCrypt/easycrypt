lemma foo2 : forall (x1:bool) (x2:bool),
(x1 => x2) => x2.
proof.
  intros x1 x2 h.
  elim h.
