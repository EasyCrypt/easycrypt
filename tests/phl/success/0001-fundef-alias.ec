require import Logic.
module M = {
  fun f () : bool = { 
    return true;
  }
}.

module N = {
  module P = M
}.

lemma foo : hoare [N.P.f : true ==> res].
proof.
 fun.
 skip.
 intros _; simplify;split.
save.