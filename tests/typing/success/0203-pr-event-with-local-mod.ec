require import Int.
require import Real.

cnst c : real.

module type I = {
  fun f (x : int) : int
}.

module G(X : I) = {
  fun f(x : int, y : int) : int = {
    return x + y;
  }
}.

lemma L : forall &m (M <: I), Pr[G(M).f(0, 0) @ &m : res = 0] = c
proof. admit. save.
