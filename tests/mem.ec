require import Int.
require import Logic.

module type Adv = { }.

module Adv(A:Adv) = {
  var n : int
  var q : int
  var g : int
}.

lemma foo :
forall z,
forall &hr,
  Adv.n{hr} + Adv.q{hr} - Adv.g{hr} = z =>
  Adv.n{hr} + Adv.q{hr} = z + Adv.g{hr}
proof.
trivial.