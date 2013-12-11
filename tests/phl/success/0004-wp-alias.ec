require import Logic.
module M = {
  var x : int
}.

module N = {
  module P = M
  proc f (z:int) : int = { 
    P.x = 2;
    return M.x;
  }
}.

lemma foo : hoare [N.f : true ==> res = 2 && N.P.x = 2 && M.x = 2].
proof.
 proc.
 wp.
 skip. 
 intros _ _.
 simplify.
 split.
save.


