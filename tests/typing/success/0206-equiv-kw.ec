require import Int.

module G = {
  fun f(x : int, y : int) : int = {
    return x + y;
  }
}.

equiv L : G.f ~ G.f : (x{1} = y{1}) ==> (0 = x{1} + y{1})
  proof.
