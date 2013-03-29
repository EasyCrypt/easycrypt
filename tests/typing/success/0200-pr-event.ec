require import Int.
require import Real.

cnst c : real.

module G = {
  fun f(x : int, y : int) : int = {
    return x + y;
  }
}.

lemma L : forall &m, Pr[G.f(0, 0) @ &m : 0 = res] = c
proof. admit. save.
