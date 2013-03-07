require import int.
require import real.

cnst c : real.

module G = {
  fun f(x : int, y : int) : int = {
    return x + y;
  }
}.

lemma L : forall {m}, Pr[f(0, 0) @ G, {m} : x + y = res] = c.
