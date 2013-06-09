require import Int.

module G = {
  fun f(x : int, y : int) : int = {
    return x + y;
  }
}.

lemma L : equiv[G.f ~ G.f : (x{1} = y{1}) ==> (0 = res{1} + res{2})].
proof. admit. save.
