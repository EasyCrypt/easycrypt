require import Real.

module type I = {
  proc f() : bool
}.

section.
  declare module A : I.

  lemma L : forall &m, Pr[A.f() @ &m : true] = 1%r.
  proof -strict. admit. qed.

end section.