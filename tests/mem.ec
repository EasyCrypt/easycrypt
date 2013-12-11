require import Int.
require import Logic.

module M = { 
  var n : int
}.

lemma foo1 : forall &m1 &m2, 
  M.n{m1} = M.n{m2} => 
  (glob M){m1} = (glob M){m2}. 
proof.
 intros &m1 &m2 H;simplify.
 smt.
qed.

module type Adv = { }.

module Adv(A:Adv) = {
  var n : int
  var q : int
  var g : int
}.


lemma foo : forall z &hr,
  Adv.n{hr} + Adv.q{hr} - Adv.g{hr} = z =>
  Adv.n{hr} + Adv.q{hr} = z + Adv.g{hr}.
proof.
prover "Alt-Ergo".
smt.
qed.