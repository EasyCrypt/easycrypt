pred p.
pred q.
pred r.

module type I = {}.

axiom A1 : true => p => q.
axiom A2 : p.
axiom A3 : q => r.

lemma L : r.
proof. by apply (A3 (:A1 _ A2)). qed.

