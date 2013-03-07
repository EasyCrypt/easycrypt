require import int.
require import real.

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

lemma L : forall {m}, Pr[f(0, 0) @ G(M), {m} : x = y] = c.
