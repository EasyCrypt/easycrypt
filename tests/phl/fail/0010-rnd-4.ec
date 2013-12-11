require import Distr. import Dinter.
require import Int. 

module G3 = {
  var z : int
  proc f() : int  = {
    z = $dinter 0 1;
    return z;
  } 
}.

module G4 = {
  var z : int
  proc f() : int  = {
    z = $dinter 1 2;
    return z;
  } 
}.

(* Should not be provable *)
equiv range_fwd : G3.f ~ G4.f : true ==> 1 <= G3.z{1} && G3.z{1} <= 2.
proof.
 proc.
 rnd.
 skip.
 smt.
