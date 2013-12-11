type t.
type u.

op ct : t.
op cu : u.

module M = {
  proc f1() : unit = {
    var x, y : t;
  }

  proc f2() : unit = {
    var (x, y) : t * u;
  }

  proc f3() : unit = {
    var x, y : t = ct;
  }

  proc f4() : unit = {
    var (x, y) : t * u = (ct, cu);
  }

  proc f5() : unit = {
    var x, y = ct;
  }

  proc f6() : unit = {
    var (x, y) = (ct, cu);
  }
}.
