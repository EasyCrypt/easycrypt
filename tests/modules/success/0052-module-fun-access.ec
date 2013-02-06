module M1 = { 
  fun F (x:int) : int = {
   return x;
  }

}.

module M2 = {
  fun M1_F (x:int) : int = {
    var r : int;
    r := M1.F (x);
    return r;
  }
}.
