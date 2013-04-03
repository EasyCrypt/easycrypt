require import Int.

lemma foo : [<=] 1 2
proof.

print op Int.[<=].

axiom toto : forall (x:int) (y:_), x = y.

print axiom toto.