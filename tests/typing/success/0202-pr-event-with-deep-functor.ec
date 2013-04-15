require import Int.
require import Real.

op c : real.

module type I = {
  fun f (x : int) : int 
}.

module type J = {
  fun f (y : int) : int
}.

module MI : I = {
  fun f (x : int) : int = { return x; }
}.

module MJ : J = {
  fun f (y : int) : int = { return y; }
}.

module G(X : I) = {
  module Inner(Y : J) = {
    fun f(x : int, y : int) : int = {
      return x + y;
    }
  }
}.

lemma L : forall &m, Pr[G(MI).Inner(MJ).f(0, 0) @ &m : 0 = res] = c
proof. admit. save.
