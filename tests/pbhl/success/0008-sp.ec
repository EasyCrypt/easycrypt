
require import Int.
module M = {
    var x : int
    var y : int

  proc test () : int = {
    var z : int;
    x = y+1;
    y = 2;
    if (x=y) { 
      z = x-y ;
    } else {
      z = 0;
    }
    return z;
  }
}
.


lemma test : equiv [M.test ~ M.test : ={M.y} ==> ={M.x} && res{1}=0].
proc.
sp.
skip.
smt.
save.

lemma test2 : hoare [M.test : M.y=0 ==> M.x=1 && res=0].
proc.
sp.
skip.
smt.
save.

require import Real.

lemma test : bd_hoare [M.test : M.y=0 ==> M.x=1 && res=0] = (1%r).
proc.
sp.
skip.
smt.
