game G = {
  fun f() : int = {
    var x :int = 1;
    while (0<x) {
      x = x-1;
    }
    return x;
  }
}.

equiv foo: G.f ~ G.f : true ==> res{2} = 0.
  while : ={x} && 0 <= x{2}; trivial.
save.

