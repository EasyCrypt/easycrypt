require import Int.
require import Real.

op c : real.

module G = {
  proc f(x y : int) : int = {
    return x + y;
  }
}.

lemma L : forall &m, Pr[G.f(0, 0) @ &m : 0 = res] = c.
proof. admit. save.
