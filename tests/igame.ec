game interface I = {
  fun foo(x : int) : int
}.

game interface I' = {
  fun bar(x : int) : int
}.

game G : I = {
  game G' : I' = {
    fun bar(x : int) : int = {
      return x;
    }
  }

  fun foo(x : int) : int = {
    return x;
  }
}.

equiv E : G:>G'.bar ~ G:>G'.bar : (true) by auto.
