(* -------------------------------------------------------------------- *)
require import AllCore.

module M = {
  proc f() = {
    var x : int;
    var y : int;

    y <- 1;
    x <- 0;
    return y;
  }
}.

op p : int -> bool.

lemma L : hoare[M.f : true ==> p res].
proof.
proc.
fail kill ^y<-.
kill ^x<-.
abort.

