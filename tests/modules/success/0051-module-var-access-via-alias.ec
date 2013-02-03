type t.

module M1 = { 
  var x : int
}.

module M = M1.

module M2 = {
  fun update_M_x (y:int) : unit = {
    M.x = y;
  }
}.
