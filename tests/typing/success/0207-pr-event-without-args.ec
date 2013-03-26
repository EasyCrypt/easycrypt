require import Real.

module G = {
  fun f(): bool = {
    return true;
  }
}.

axiom L: forall {m}, Pr[ f() @ G, {m}: res] = 1%r.
