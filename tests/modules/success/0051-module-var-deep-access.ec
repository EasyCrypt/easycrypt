module M1 = { 
  module I = {
    var x : int
  }
}.

module M2 = {
  proc update_M1_x (y:int) : unit = {
    M1.I.x = y;
  }
}.
