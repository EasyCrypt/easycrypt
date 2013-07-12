require import Bool.
 
module type O = {
  fun g() : bool
}.
 
module type AF(O : O) = {
  fun f(x : bool) : bool
}.
 
module M(AF : AF) = {
  module I = {
    fun g() : bool = {
      return true;
    }
  }
  
  module A = AF(I)
 
  fun main() : bool = {
    var b : bool;
    b = A.f(true);
    return true;
  }
}.
 
lemma triv:
    forall (A <: AF {M}),
  equiv[ M(A).main ~ M(A).main : ={glob A} ==> ={res} ].
proof.
  intros=> A.
  fun.
  call (_ : true) => //.
  fun => //.
qed.