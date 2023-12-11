(* -------------------------------------------------------------------- *)
require import AllCore.

(* -------------------------------------------------------------------- *)
module M = {
  proc f(x : int, y : int) : int = {
    var z : int <- x * (x + y);
    return z;
  }
}.

(* -------------------------------------------------------------------- *)
lemma L x0 y0 : hoare[M.f : arg = (x0, y0) ==> res = (y0 + x0) * x0].
proof.
proc.
proc rewrite 1 addzC.
proc rewrite 1 mulzC.
auto=> />.
qed.
