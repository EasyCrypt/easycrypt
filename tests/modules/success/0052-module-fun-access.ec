type t.

module M1 = { 
  fun f (x : t) : t = {
   return x;
  }
}.

module M2 = {
  fun m1_f (x : t) : t = {
    var r : t;

    r := M1.f(x);
    return r;
  }
}.
