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
equiv equality : G3.f ~ G4.f : true ==> true.
proof.
 proc.
 rnd.
 skip.
 smt.
