require import Distr. import Dinter.
require import Int. 

module G1 = {
  fun f() : bool = {
    var z : int;
    z = $dinter 0 0;
    return true;
  } 
}.

module G2 = {
  fun f() : bool = {
    var z : int;
    var b : bool = false;
    z = $dinter 0 0;
    if (z = 1) { b = true; }
    return b;
  } 
}.

(* Should not be provable *)
equiv forward : G1.f ~ G2.f : true ==> true 
proof.
 fun.
 wp.
 rnd (lambda z, 1 - z).
 wp.
 skip.
 trivial.



