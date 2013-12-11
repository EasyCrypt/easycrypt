require import Int.
require import Real.

module M = {
  proc f(x : int, y : int) : int = {
    var r : int = x + y;
    return r;
  }

  proc g(a : int) : int = {
    var z : int;

    z  = f(a, a);
    return z;
  }
}.

lemma h : bd_hoare[M.g : a = a ==> res = res] = 1%r.
proof.
  proc; inline M.f. wp; skip; smt.
save.
