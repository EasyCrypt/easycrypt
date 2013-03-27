require import Real.

module G = {
  fun f(): bool = {
    return true;
  }
}.

axiom L: forall &m, Pr[G.f() @ &m: res] = 1%r.
