type t.

module M1 = { 
  fun F (x : t) : t = {
   return x;
  }
}.

module M2 = {
  fun M1_F (x : t) : t = {
    var r : t;

    r := M1.F(x);
    return r;
  }
}.
