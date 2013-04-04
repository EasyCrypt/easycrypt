require Logic.
module M = {
  fun f (w x:int) : int = {
    var y, z : int;
    y = 1;
    z = x;
    x = y;
    y = z; 
    return x;
  }
}.

lemma foo : hoare [M.f : true ==> res = 1 ]
proof.
 fun.
 wp.
 skip;intros _ _;split.
save.

lemma foo1 : hoare [M.f : true ==> res = 1 ]
proof.
 fun.
 wp 1.
 wp 0.
 skip;intros _ _;split.
save.

    