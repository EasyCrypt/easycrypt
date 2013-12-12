module type OR = {
  proc f() : int
}.

module Or : OR = {
  proc f() : int = {
    return 3;
  }
}.

module type ADV1(Or : OR) = {
  proc * g() : int { Or.f}
}.

module type ADV2(Or : OR) = {
  proc * h() : int { Or.f}
}.

module G(Adv2 : ADV2) = {
  module A = Adv2(Or)

  proc g() : int = {
    var n : int;
    n = A.h();
    return n;
  }
}.

(* Same remark than 0017_init_adv2.ec could be greate to see that the
   restriction Or in not needed since Or do not have state *)
lemma G :
  forall (Adv2 <: ADV2{Or}),
  (forall (O <: OR{Adv2}), islossless O.f => islossless Adv2(O).h) =>
  equiv[G(Adv2).g ~ G(Adv2).g : true ==> ={res}].
proof -strict.
intros Adv2 LossAdv2.
proc.
call (_ : true ==> ={res, glob Adv2}).
(* I'm using three argument proc here just to test losslessness *)
proc (false) (true) (true).
trivial. trivial. assumption LossAdv2.
proc; skip; trivial.
trivial.
intros &1; proc; skip; trivial.
skip; trivial.
qed.

section.

declare module Adv1 : ADV1{Or}.

local module FAdv2(Adv1:ADV1, Or : OR) = {
  module A = Adv1(Or)

  proc h() : int = {
    var n : int;
    n = A.g();
    return n;
  }
}.

local module Adv2 = FAdv2(Adv1).

local lemma G_Inst :
  (forall (O <: OR{Adv2}), islossless O.f => islossless Adv1(O).g) =>
  equiv[G(Adv2).g ~ G(Adv2).g : true ==> ={res}].
proof -strict.
intros LossAdv1.
apply (G (Adv2)).
intros O LossF.
proc.
 call (LossAdv1 O _);trivial.
qed.

axiom G' :
  forall (Adv2 <: ADV2{Or}),
  (forall (O <: OR), islossless O.f => islossless Adv2(O).h) =>
  equiv[G(Adv2).g ~ G(Adv2).g : true ==> ={res}].

local lemma G_Inst' :
  (forall (O <: OR), islossless O.f => islossless Adv1(O).g) =>
  equiv[G(Adv2).g ~ G(Adv2).g : true ==> ={res}].
proof -strict.
intros LossAdv1.
apply (G' (Adv2)).
intros O LossF.
proc.
 call (LossAdv1 O _);trivial.
qed.

end section.


