require import AllCore.

type t = int.
op dint : t distr.

module M = {
  var x : t

  proc f1() : unit = {
    M.x <- 0;
  }

  proc f2(a: int) : unit = {
    M.x <- a;
  }

  proc f3(a: int, b: int) : int = {
    return a + b;
  }

  proc f4(a: int, b: int) : int = {
    var t;
    if (a <= b) {
      t <- b;
    } else {
      t <- a;
    }
    return t;
  }

  proc f5(d: int distr) : int = {
    var v;
    v <$ d;
    return v;
  }
}.


module N = {
  proc g1() : unit = {
    M.f1();
  }

  proc g2(a) : unit = {
    M.f2(a);
  }

  proc g3(a, b) : unit = {
    var r;
    r <@ M.f3(a, b);
  }

  proc g4(a: int, b: int) : unit = {
    var m;
    if (a <= b) {
      m <- b;
    } else {
      m <- a;
    }
    M.x <- m;
  }

  proc g5() : unit = {
    var x;
    x <$ dint;
  }

  proc g6() : unit = {
    var a, b, m;
    a <$ dint;
    b <$ dint;
    if (a <= b) {
      m <- b;
    } else {
      m <- a;
    }
    M.x <- m;
  }
}.

equiv outline_no_args_no_ret: N.g1 ~ N.g1: true ==> true.
proc.
inline {1} 1.
outline {1} 1 M.f1.
by sim.
qed.

equiv outline_no_ret: N.g2 ~ N.g2: true ==> true.
proc.
inline {1} 1.
outline {1} 2 M.f2.
by inline*; auto.
qed.

equiv outline_no_body: N.g3 ~ N.g3: true ==> true.
proc.
inline {1} 1.
outline {1} 3 M.f3.
by inline*; auto.
qed.

equiv outline_slice: N.g4 ~ N.g4: true ==> true.
proc.
outline {1} [1 .. 2] M.f4.
by inline*; auto.
qed.

equiv outline_explicit_ret: N.g5 ~ N.g5: true ==> true.
proc.
outline {1} 1 ~ M.f5.
by inline*; auto.
qed.

equiv outline_multi: N.g6 ~ N.g6: true ==> true.
proof.
proc.
outline {1} 2 ~ M.f5.
outline {1} [3 .. 4] N.g4.
outline {1} 1 ~ M.f5.
by inline*; auto.
qed.

equiv outline_stmt: N.g6 ~ N.g6: true ==> true.
proof.
proc.
outline {1} [1 .. 4] by {
  a <@ M.f5(dint);
  b <@ M.f5(dint);
  N.g4(a,b);
}.
by inline*; auto.
qed.
