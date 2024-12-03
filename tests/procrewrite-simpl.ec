require import AllCore.

module M = {
  proc f(x : int) : int = {
    x <- x * 0;
    return x;
  }
}.

lemma L : hoare[M.f : true ==> true].
proof.
proc.
proc rewrite 1 /=.
abort.
