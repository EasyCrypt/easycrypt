require import Real.

module type I = {
  fun f() : bool
}.

section.
  declare module A : I.

  lemma L : forall &m, Pr[A.f() @ &m : true] = 1%r.
  proof. admit. qed.

end section.