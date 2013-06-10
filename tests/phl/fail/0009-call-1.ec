require Logic.

module M = {
  var y : int
  var z : int
  fun f (x:int) : int = { 
    y = x;
    return 3;
  }
}.

lemma foo : 
  hoare [M.f : true ==> true].
proof.
 fun.
 call true true. 