require import Int.
require import Real.

op c : real.

module type I = {
  proc f (x : int) : int
}.

module G(X : I) = {
  proc f(x y : int) : int = {
    return x + y;
  }
}.

lemma L : forall &m (M <: I), Pr[G(M).f(0, 0) @ &m : res = 0] = c.
proof. admit. qed.
