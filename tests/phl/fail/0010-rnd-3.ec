require import Distr. import Dinter.
require import Int. 

module G1 = {
  proc f() : bool = {
    var z : int;
    z = $dinter 0 0;
    return true;
  } 
}.

module G2 = {
  proc f() : bool = {
    var z : int;
    var b : bool = false;
    z = $dinter 0 0;
    if (z = 1) { b = true; }
    return b;
  } 
}.

(* Should not be provable *)
equiv backward : G1.f ~ G2.f : true ==> true.
proof -strict. 
 proc.
 wp.
 rnd (fun z, 1 - z), (fun z, 1 - z).
 wp.
 skip.
 smt.


