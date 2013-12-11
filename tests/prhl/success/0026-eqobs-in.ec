require import Int.

module O = { 
  var m : int
  var l : int
  proc o (x:int) : int = {
    m = x + m;
    return m;
  }
}.

module G = {
  proc main (x:int) : int = { 
    x = O.o(x);
    return x;
  }
}.

equiv foo_0 : G.main ~ G.main : ={x, glob O} ==> ={res, glob O}.
proc.
eqobs_in : (={x,glob O}).
save.