game H = {
  var m : (int, int) map
  fun O(h:int) : int = {
    if (!in_dom(h, m)) { m[h] = [0..k]; }
    return m[h];
  }
}.

game Lazy = {
  fun H(x:int) : int = {
    var r : int;
    r = H.O(x);
    return r;
  }
}.


(*
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

print G.
*)
