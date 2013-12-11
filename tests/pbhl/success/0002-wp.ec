require import Logic.
require import Distr.
require import Bool.
require import Real.


require Logic.
module M = {
  proc f (w x:int) : int = {
    var y : int;
    var z : int;
    y = 1;
    z = x;
    x = y;
    y = z; 
    return x;
  }
}.
lemma test : phoare [M.f : true ==> res = 1 ] >= 1%r.
 proc.
 wp.
 skip;intros _ _;split.
qed.

op b : bool.

module M2 = {
  var z : bool
  proc f (y:bool) : bool = {
    var x : bool;
    x = $Dbool.dbool;
    if (b)  z = x;
    return z=y;
  }
}.

lemma test2: phoare [ M2.f : b ==> res] = (1%r/2%r). 
proc.
wp.
rnd ((=) y).
skip.
simplify.
intros &hr b.
split;[smt|smt].
qed.


module M3 = {
  var z : bool
  proc f (y:bool) : bool = {
    var x : bool;
    x = $Dbool.dbool;
    if (x<>b)  x = !x;
    return x;
  }
}.

lemma test3: phoare [ M3.f : true ==> res=b] >= 1%r. 
proof.
proc.
wp.
rnd (fun x, true) .
skip; smt.
qed.



module M4 = {
  var x : real
  var y : bool
  proc foo () : unit = {
    if (true) {
      y = ${0,1};
    }
    x = 1%r; 
  }
}
.

require import Real.
lemma test : phoare[M4.foo : M4.x=(Real.(/) 1%r2%r) ==> M4.y=true] = M4.x.
proc.
wp.
rcondt 1; [trivial|].
rnd;skip; smt.
