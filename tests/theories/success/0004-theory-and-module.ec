theory Th.
  module M1 = {
    var x : int

    module N1 = {
      var y : int
    }
  }.

  module M2 = {
    proc u () : int = {
      return M1.x;
    }
  }.

  module M3 = {
    proc u () : int = {
      return M1.N1.y;
    }
  }.
end Th.

module M2' = {
    proc u () : int = {
      return Th.M1.x;
    }
}.

module M3' = {
  proc u () : int = {
     return Th.M1.N1.y;
  }
}.
