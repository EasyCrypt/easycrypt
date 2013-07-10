module type OR = {
  fun f() : int
}.

module Or : OR = {
  fun f() : int = {
    return 3;
  }
}.

module type ADV1(Or : OR) = {
  fun g() : int {* Or.f}
}.

module type ADV2(Or : OR) = {
  fun h() : int {* Or.f}
}.

module G(Adv2 : ADV2) = {
  module A = Adv2(Or)

  fun g() : int = {
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
proof.
intros Adv2 LossAdv2.
fun.
call (_ : true ==> ={res, glob Adv2}).
(* I'm using three argument fun here just to test losslessness *)
fun (false) (true) (true).
trivial. trivial. assumption LossAdv2.
fun; skip; trivial.
trivial.
intros &1; fun; skip; trivial.
skip; trivial.
qed.

section.

declare module Adv1 : ADV1{Or}.

module Adv2(Adv1:ADV1, Or : OR) = {
  module A = Adv1(Or)

  fun h() : int = {
    var n : int;
    n = A.g();
    return n;
  }
}.

lemma G_Inst :
  (forall (O <: OR{Adv2(Adv1)}), islossless O.f => islossless Adv1(O).g) =>
  equiv[G(Adv2(Adv1)).g ~ G(Adv2(Adv1)).g : true ==> ={res}].
proof.
intros LossAdv1.
apply (G (Adv2(Adv1))).
intros O LossF.
fun.
 call (LossAdv1 O _);trivial.
save.
