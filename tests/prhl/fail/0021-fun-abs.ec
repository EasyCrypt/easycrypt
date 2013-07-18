module type OR = {
  fun f() : unit
}.

module type ADV(O : OR) = {
  fun g() : int { O.f}
}.

module Adv(O : OR) : ADV(O) = {
  var x : int
  fun g() : int = {
    O.f();
    return x;
  }
}.

module Or1 : OR = {
  fun f() : unit = {
    Adv.x = 0;
  }
}.

module Or2 : OR = {
  fun f() : unit = {
  }
}.

module G1(Adv : ADV) = {
  module A = Adv(Or1)

  fun main() : int = {
    var y : int;
    y = A.g();
    return y;
  }
}.

module G2(Adv : ADV) = {
  module A = Adv(Or2)

  fun main() : int = {
    var y : int;
    y = A.g();
    return y;
  }
}.

lemma G1_G2 (Adv' <: ADV{Adv}) :
  equiv[G1(Adv').main ~ G2(Adv').main : ={glob Adv'} ==> ={res}].
proof.
fun.
call (_ : ={glob Adv'} ==> ={res}).
fun (true);trivial.
fun;wp;skip; trivial.
skip; trivial.
qed.

lemma G1_G2_Adv :
  equiv[G1(Adv).main ~ G2(Adv).main : ={glob Adv} ==> ={res}].
proof.
(* should fail here *)
apply (G1_G2 Adv). 
qed.