module type OR = {
  proc f() : unit
}.

module type ADV(O : OR) = {
  proc g() : int { O.f}
}.

module Adv(O : OR) : ADV(O) = {
  var x : int
  proc g() : int = {
    O.f();
    return x;
  }
}.

module Or1 : OR = {
  proc f() : unit = {
    Adv.x = 0;
  }
}.

module Or2 : OR = {
  proc f() : unit = {
  }
}.

module G1(Adv : ADV) = {
  module A = Adv(Or1)

  proc main() : int = {
    var y : int;
    y = A.g();
    return y;
  }
}.

module G2(Adv : ADV) = {
  module A = Adv(Or2)

  proc main() : int = {
    var y : int;
    y = A.g();
    return y;
  }
}.

lemma G1_G2 (Adv' <: ADV) :
  equiv[G1(Adv').main ~ G2(Adv').main : ={glob Adv'} ==> ={res}].
proof -strict.
proc.
call (_ : ={glob Adv'} ==> ={res}).
proc (true);trivial.
proc.
(* should fail here *)
wp. 
skip; trivial.
skip; trivial.
qed.

