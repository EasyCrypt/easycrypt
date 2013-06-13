require import Int.

module M = {
  fun f(x : int, y : int) : int = {
    var r : int = x + y;
    return r;
  }

  fun g(a : int) : int = {
    var z : int;

    z  = f(a, a);
    return z;
  }
}.

lemma h : hoare[M.g : a = a ==> res = res].
proof.
  fun; inline M.f. wp; skip; trivial.
save.
