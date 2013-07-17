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
rnd ((=) y).
skip.
simplify.
intros &hr b.
split;[smt|smt].
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
rnd (lambda x, true) .
skip; smt.
save.



module M4 = {
  var x : real
  var y : bool
  fun foo () : unit = {
    if (true) {
      y = ${0,1};
    }
    x = 1%r; 
  }
}
.

require import Real.
lemma test : bd_hoare[M4.foo : M4.x=(Real.(/) 1%r2%r) ==> M4.y=true] = M4.x.
fun.
wp.
rcondt 1; [trivial|].
rnd;skip; smt.
