require import Int.

module M = { 
  var i, j : int
  proc f (x:int) : int = {
    i = 0;
    while (i < 10) {
      x = i + x;
      i = i + 1;
    }
    return x;
  }
}.

module M' = { 
  var i, j : int
  proc f (x:int) : int = {
    i = 0; j = 0;
    while (j < 10) {
      x = i + x;
      j = j + 1;
    }
    return x;
  }
}.

equiv foo : M.f ~ M'.f : ={x} ==> ={res}.
proc.
seq 1 2 : true.
 wp => //.
sim.
skip.


