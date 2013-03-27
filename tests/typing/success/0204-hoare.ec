require import Int.

module G = {
  fun f(x : int, y : int) : int = {
    return x + y;
  }
}.

lemma L : hoare[G.f : (x = y) ==> (res = x + y)]
proof. admit. save.
