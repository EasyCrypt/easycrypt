
require import Real.

module type Adv = {
  proc f(x:int) : bool
}.


module M(A:Adv) = {

  proc f(x:int) : bool = {
    return x=5;
  }
  
  proc g() : bool = {
    var b : bool;
    b = A.f(5);
    return b;
  }

}.

lemma foo : forall (A<:Adv),
  hoare [M(A).g : true ==> true].
intros A.
proc.
call ( _ : true ==> true).


lemma foo : forall (A<:Adv),
  phoare [M(A).g : true ==> true] = 1%r.
intros A.
proc.
call ( _ : true ==> true).

