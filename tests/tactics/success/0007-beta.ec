lemma l: forall (x:int), (lambda y, y = y) x.
proof.
beta.
trivial.
save.