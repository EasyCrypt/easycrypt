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
 admit.
save.

lemma foo1 : hoare [M.f : true ==> res = 1 ]
proof.
 fun.
 wp 3.
 admit.
save.

    