require import AllCore.

module type I = {
  proc bar(x : int) : int
}.

module N : I = {
  proc bar(x : int) : int = {
    return 2*x;
  }
}.

module M(O : I) = {
  proc foo(x : int, y : int) : int = {
    var z, t, u;

    (z, t) <- (2 * x, 3 * y);

    if (x-1 = 1) {
      y <- y + 1;
    }

    while (0 < x) {
      z <- z + 2;
      x <- x - 1;
    }

    u <@ O.bar(y);

    return x + y + z * t + u;
  }
}.

eval M(N).foo(2, 3).
