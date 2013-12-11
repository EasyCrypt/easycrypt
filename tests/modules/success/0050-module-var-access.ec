module M1 = { 
  var x : int
}.

module M2 = {
  proc update_M1_x (y:int) : unit = {
    M1.x = y;
  }
}.
