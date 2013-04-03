require Logic.

lemma foo : forall (a b : bool), a /\ !(1=2) => a
proof.
 simplify.
 intros a b h.
 elim h.

print op Int.[<=].

axiom toto : forall (x:int) (y:_), x = y.

print axiom toto.