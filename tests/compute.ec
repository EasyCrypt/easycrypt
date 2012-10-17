game G = {
  var x, y : int

  fun f (b:bool) : bool = {
    var b' : bool = {0,1};
    return b = b';
  }
}.

prover "alt-ergo".

claim test : G.f[res && x <= y] <= 1%r/2%r * G.f[x < y || x = y]
compute.

game GW = {
  var x, y : int

  fun f (b:bool) : bool = {
    var b' : bool;
    while (x < y) { x = x + 1; }
    b' = {0,1};
    return b = b';
  }
}.

claim testW : GW.f[res && x <= y] <= 1%r/2%r * GW.f[x < y || x = y]
compute.
