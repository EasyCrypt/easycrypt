
require import Real.

module type Adv = {
  fun f(x:int) : bool
}.


module M(A:Adv) = {

  fun f(x:int) : bool = {
    return x=5;
  }
  
  fun g() : bool = {
    var b : bool;
    b = A.f(5);
    return b;
  }

}.

lemma foo : forall (A<:Adv),
  hoare [M(A).g : true ==> true].
intros A.
fun.
call true true.


lemma foo : forall (A<:Adv),
  bd_hoare [M(A).g : true ==> true] = 1%r.
intros A.
fun.
call true true.

