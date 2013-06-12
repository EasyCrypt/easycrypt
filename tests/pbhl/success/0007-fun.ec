
require import Real.

module type Adv = {
  fun f() : unit
}.


module M(A:Adv) = {

  fun g() : unit = {
    A.f();
  }

}.


lemma foo : forall (A<:Adv),
  bd_hoare [M(A).g : true ==> true] = 1%r
proof.
intros A.
fun.
call true true.

