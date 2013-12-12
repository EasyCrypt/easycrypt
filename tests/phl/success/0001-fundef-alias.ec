require import Logic.
module M = {
  proc f () : bool = { 
    return true;
  }
}.

module N = {
  module P = M
}.

lemma foo : hoare [N.P.f : true ==> res].
proof -strict.
 proc.
 skip.
 intros _; simplify;split.
qed.