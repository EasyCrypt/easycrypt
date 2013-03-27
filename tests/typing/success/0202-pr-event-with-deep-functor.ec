require import Int.
require import Real.

cnst c : real.

module type I = {
  var x : int
}.

module type J = {
  var y : int
}.

module MI : I = {
  var x : int
}.

module MJ : J = {
  var y : int
}.

module G(X : I) = {
  module Inner(Y : J) = {
    fun f(x : int, y : int) : int = {
      return x + y;
    }
  }
}.

lemma L : forall &m, Pr[G(MI).Inner(MJ).f(0, 0) @ &m : x = y] = c
proof. admit. save.
