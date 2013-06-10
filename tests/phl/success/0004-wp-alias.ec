require import Logic.
module M = {
  var x : int
}.

module N = {
  module P = M
  fun f (z:int) : int = { 
    P.x = 2;
    return M.x;
  }
}.

lemma foo : hoare [N.f : true ==> res = 2 && N.P.x = 2 && M.x = 2].
proof.
 fun.
 wp.
 skip. 
 intros _ _.
 simplify.
 split.
save.


