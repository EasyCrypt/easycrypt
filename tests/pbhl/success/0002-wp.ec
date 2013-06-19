require import Logic.
require import Distr.
require import Bool.
require import Real.


require Logic.
module M = {
  fun f (w x:int) : int = {
    var y : int;
    var z : int;
    y = 1;
    z = x;
    x = y;
    y = z; 
    return x;
  }
}.
lemma test : bd_hoare [M.f : true ==> res = 1 ] >= 1%r.
 fun.
 wp.
 skip;intros _ _;split.
save.

op b : bool.

module M2 = {
  var z : bool
  fun f (y:bool) : bool = {
    var x : bool;
    x = $Dbool.dbool;
    if (b)  z = x;
    return z=y;
  }
}.

lemma test2: bd_hoare [ M2.f : b ==> res] = (1%r/2%r). 
fun.
wp.
rnd (1%r/2%r) (lambda (x:bool), x=y).
skip.
intros _ n; split; [smt|smt].
save.


module M3 = {
  var z : bool
  fun f (y:bool) : bool = {
    var x : bool;
    x = $Dbool.dbool;
    if (x<>b)  x = !x;
    return x;
  }
}.

lemma test3: bd_hoare [ M3.f : true ==> res=b] >= 1%r. 
proof.
fun.
wp.
rnd 1%r (lambda x, true) .
skip; smt.
save.









