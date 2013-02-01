module M1 = { 
  var x : int
}.

module M2 = {
  fun upd_x (y:int) : unit = {
    M1.x = y;
  }
}.