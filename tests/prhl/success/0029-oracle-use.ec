require import Bool.
 
module type O = {
  proc g() : bool
}.
 
module type AF(O : O) = {
  proc f(x : bool) : bool
}.
 
module M(AF : AF) = {
  module I = {
    proc g() : bool = {
      return true;
    }
  }
  
  module A = AF(I)
 
  proc main() : bool = {
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
  proc.
  call (_ : true) => //.
  proc => //.
qed.