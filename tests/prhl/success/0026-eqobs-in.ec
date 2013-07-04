require import Int.

module O = { 
  var m : int
  var l : int
  fun o (x:int) : int = {
    m = x + m;
    return m;
  }
}.

module G = {
  fun main (x:int) : int = { 
    x = O.o(x);
    return x;
  }
}.

equiv foo_0 : G.main ~ G.main : ={x, glob O} ==> ={res, glob O}.
fun.
eqobs_in : (={x,glob O}).
save.