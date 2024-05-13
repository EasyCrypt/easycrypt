(* -------------------------------------------------------------------- *)
require import AllCore.

(* -------------------------------------------------------------------- *)
module M = {
  proc f(a : int, b : int) : int = {
    var c : int <- a * (a + b);
    return c;
  }
}.

(* -------------------------------------------------------------------- *)
lemma L a0 b0 : hoare[M.f : arg = (a0, b0) ==> res = (b0 + a0) * a0].
proof.
proc.
proc rewrite 1 addzC.
proc rewrite 1 mulzC.
auto=> />.
qed.
