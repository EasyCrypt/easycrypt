require import int.
require import real.

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

lemma L : forall {m}, Pr[f(0, 0) @ G(MI).Inner(MJ), {m} : x = y] = c.
