require import int.

module G = {
  fun f(x : int, y : int) : int = {
    return x + y;
  }
}.

lemma L : Pr[f(0, 0) @ G, {m} : x = y] = Pr[f(0, 0) @ G, {m} : x = y].

