require import Int.

module G1 = {
  var u : int

  fun f(x : int) : int = {
    x = x + 1;
    x = x + 2;
    x = x - 1;
    u = u + 1 + x;
    return x;
  }

  fun main (x:int) : int = { 
    var y, z : int;
    u = 10;
    y = f(x);
    z = f(y);
    return z;
  }
}.

module G2 = {
  var u : int

  fun f(x : int) : int = {
    x = x + 1;
    x = x + 1;
    u = u + 1 + x;
    return x;
  }

  fun main (x:int) : int = { 
    var y, z : int;
    u = 10;
    y = f(x);
    z = f(y);
    return z;
  }
}.

lemma G1_G2_main :
  equiv[G1.main ~ G2.main : ={x} ==> ={res}].
proof.
fun.
eqobs_in (G1.u{1} = G2.u{2}) true : (={z} /\ G1.u{1} = G2.u{2}).
 fun; wp; skip; smt.
save.

