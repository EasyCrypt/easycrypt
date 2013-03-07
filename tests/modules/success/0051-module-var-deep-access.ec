module M1 = { 
  module I = {
    var x : int
  }
}.

module M2 = {
  fun update_M1_x (y:int) : unit = {
    M1.I.x = y;
  }
}.
