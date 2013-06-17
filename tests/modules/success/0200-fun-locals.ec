type t.
type u.

op ct : t.
op cu : u.

module M = {
  fun f1() : unit = {
    var x, y : t;
  }

  fun f2() : unit = {
    var (x, y) : t * u;
  }

  fun f3() : unit = {
    var x, y : t = ct;
  }

  fun f4() : unit = {
    var (x, y) : t * u = (ct, cu);
  }

  fun f5() : unit = {
    var x, y = ct;
  }

  fun f6() : unit = {
    var (x, y) = (ct, cu);
  }
}.
