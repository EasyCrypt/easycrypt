require import AllCore Xreal.

module M = {
  proc f() : int = {
    var x;
    x <- 1;
    x <- x + 1;
    return x;
  }
}.

lemma L : ehoare [M.f : (1%xr) ==> (1%xr)].
proof.
proc.
seq 1 : (1%xr).
+ by wp; skip.
by wp; skip.
qed.

lemma Lerr1 : ehoare [M.f : (1%xr) ==> (1%xr)].
proof.
proc.
fail seq 1 1 : (1%xr).
fail seq 1 : (1%xr) (1%xr).
abort.
