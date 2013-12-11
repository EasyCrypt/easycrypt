require import Int.
require import Real.

op c : real.

module type I = {
  proc f (x : int) : int
}.

module M : I = {
  proc f (x : int) : int = {
    return x;
  }
}.

module G(X : I) = {
  proc f(x : int, y : int) : int = {
    return x + y;
  }
}.

lemma L : forall &m, Pr[G(M).f(0, 0) @ &m : res = 0] = c.
proof. admit. save. 
