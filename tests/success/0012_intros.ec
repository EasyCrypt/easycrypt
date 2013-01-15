lemma toto : forall (p:bool), p => p
proof.
  intros p H.
  assumption H.
save.