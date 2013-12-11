require import Int.

module M1 = { 
  var i, j : int
  proc f (x:int) : int = {
    i = 0; j = 0;
    while (i < 10) {
      x = i;
      i = i;
    }
    return x;
  }
}.

module M1' = { 
  var i, j : int
  proc f (x:int) : int = {
    i = 0; j = 0;
    while (j < 10) {
      x = i;
      j = j;
    }
    return x;
  }
}.

equiv foo : M1.f ~ M1'.f : ={x} ==> ={res}.
proc.
sim.
wp => //.
save.



