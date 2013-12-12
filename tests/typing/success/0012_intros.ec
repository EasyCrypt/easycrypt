lemma toto : forall (p:bool), p => p.
proof -strict.
  intros p H.
  assumption H.
qed.