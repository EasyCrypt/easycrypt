require import Int.

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

lemma h : hoare[M.g : a = a ==> res = res].
proof.
  proc; inline M.f. wp; skip; smt.
save.
