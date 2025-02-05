(* -------------------------------------------------------------------- *)
require import AllCore.

module M = {
  proc f() = {
    var x : int;
    var y : int;
    var z : int;

    y <- 1;
    (x, z) <- (0, 0);
    return y;
  }
}.

op p : int -> bool.

lemma L : hoare[M.f : true ==> p res].
proof.
proc.
swap ^()<- @ ^y<-.
swap ^y<- @ ^(x)<-.
abort.
