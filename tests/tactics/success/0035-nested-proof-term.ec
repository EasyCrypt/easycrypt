(* -------------------------------------------------------------------- *)
pred p.
pred q.
pred r.

module type I = {}.

axiom A1 : true => p => q.
axiom A2 : p.
axiom A3 : forall &m, q => r.
axiom A4 : (true /\ true) => forall (M <: I), true.

lemma L &m (M <: I) : r.
proof. by apply (A3 &m (A1 (A4 _ M) A2)). qed.
