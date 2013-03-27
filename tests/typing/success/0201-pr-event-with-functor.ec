require import Int.
require import Real.

cnst c : real.

module type I = {
  var x : int
}.

module M : I = {
  var x : int
}.

module G(X : I) = {
  fun f(x : int, y : int) : int = {
    return x + y;
  }
}.

lemma L : forall {m}, Pr[G(M).f(0, 0) @ {m} : x = y] = c
proof. admit. save.
