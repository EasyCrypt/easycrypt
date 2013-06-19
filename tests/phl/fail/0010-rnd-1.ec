require import Distr. import Dinter.
require import Int. 

module G0 = {
  fun f() : int = {
    var z : int;
    z = $dinter 0 0;
    return z;
  } 
}.

(* Should not be provable *)
equiv minimal : G0.f ~ G0.f : true ==> res{1} < res{2}.
proof.
 fun.
 rnd (lambda z, z-1) , (lambda z, z+1).
 skip. 
 smt.  
