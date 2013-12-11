type t.

module M1 = { 
  proc f (x : t) : t = {
   return x;
  }
}.

module M2 = {
  proc m1_f (x : t) : t = {
    var r : t;

    r  = M1.f(x);
    return r;
  }
}.
