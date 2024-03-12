require import AllCore.

module M = {
  proc f(x : int) = {
    x <- x + 0;
  }
}.

lemma L : equiv[M.f ~ M.f : true ==> true].
proof.
proc.
proc change {1} 1 : x.
- smt().
abort.
