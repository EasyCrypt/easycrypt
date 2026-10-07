(* -------------------------------------------------------------------- *)
(* Side conditions of loop fission / fusion:

     init; while b { c1; c2; c3 }
       ==  init; while b { c1; c3 }; init; while b { c2; c3 }       *)
require import AllCore DBool.

exception oops.

(* -------------------------------------------------------------------- *)
module N = {
  var x, y, z : int
  var b1, b2  : bool

  (* the second prelude would reset [z], written by c1 = [z <- 5] *)
  proc f1() = {
    var i;
    i <- 0;
    z <- 0;
    while (i < 1) {
      z <- 5;
      i <- i + 1;
    }
  }

  (* the epilog [x <- x + 1; i <- i + 1] would run twice: [x] is not
     reset by the prelude *)
  proc f2() = {
    var i;
    i <- 0;
    while (i < 1) {
      x <- x + 1;
      i <- i + 1;
    }
  }

  (* c1 = [x <- i] and c2 = [if (i = 0) x <- 7] both write [x] *)
  proc f3() = {
    var i;
    i <- 0;
    while (i < 2) {
      x <- i;
      if (i = 0) { x <- 7; }
      i <- i + 1;
    }
  }

  (* c1 raises after one execution of c2 *)
  proc f4() = {
    var i;
    i <- 0;
    while (i < 2) {
      if (i = 1) { raise oops; }
      y <- y + 1;
      i <- i + 1;
    }
  }

  (* the prelude samples [r], read by c1 and c2 *)
  proc f5() = {
    var i, r;
    i <- 0;
    r <$ {0,1};
    while (i < 1) {
      b1 <- r;
      b2 <- r;
      i <- i + 1;
    }
  }

  (* fusing would drop the second reset of [z] *)
  proc g1() = {
    var i;
    i <- 0;
    z <- 0;
    while (i < 1) {
      z <- 5;
      i <- i + 1;
    }
    i <- 0;
    z <- 0;
    while (i < 1) {
      i <- i + 1;
    }
  }

  (* fusing would merge the two samplings of [r] *)
  proc g5() = {
    var i, r;
    i <- 0;
    r <$ {0,1};
    while (i < 1) {
      b1 <- r;
      i <- i + 1;
    }
    i <- 0;
    r <$ {0,1};
    while (i < 1) {
      b2 <- r;
      i <- i + 1;
    }
  }
}.

lemma L1 : hoare [N.f1 : true ==> N.z = 5].
proof. proc. fail fission 3!2 @ 1, 1. abort.

lemma L2 : hoare [N.f2 : N.x = 0 ==> N.x = 1].
proof. proc. fail fission 2 @ 0, 0. abort.

lemma L3 : hoare [N.f3 : true ==> N.x = 1].
proof. proc. fail fission 2 @ 1, 2. abort.

lemma L4 : hoare [N.f4 : N.y = 0 ==> false | oops => N.y = 1].
proof. proc. fail fission 2 @ 1, 2. abort.

lemma L5 : hoare [N.f5 : true ==> N.b1 = N.b2].
proof. proc. fail fission 3!2 @ 1, 2. abort.

lemma G1 : hoare [N.g1 : true ==> N.z = 0].
proof. proc. fail fusion 3!2 @ 1, 0. abort.

lemma G5 : hoare [N.g5 : true ==> N.b1 = N.b2].
proof. proc. fail fusion 3!2 @ 1, 1. abort.

(* -------------------------------------------------------------------- *)
module L = {
  var n, x, y : int
  var b       : bool

  proc f() = {
    var i, j;
    i <- 0;
    j <- 0;
    y <- 0;
    while (i < n) {
      x <- x + j;
      b <$ {0,1};
      y <- y + j;
      i <- i + 1;
      j <- j + 2;
    }
  }

  proc g() = {
    var i, j;
    i <- 0;
    j <- 0;
    y <- 0;
    while (i < n) {
      x <- x + j;
      b <$ {0,1};
      i <- i + 1;
      j <- j + 2;
    }
    i <- 0;
    j <- 0;
    y <- 0;
    while (i < n) {
      y <- y + j;
      i <- i + 1;
      j <- j + 2;
    }
  }
}.

equiv fission_ok : L.f ~ L.g : ={L.n, L.x, L.y, L.b} ==> ={L.n, L.x, L.y, L.b}.
proof. proc; fission{1} 4!3 @ 2, 3; sim. qed.

equiv fusion_ok : L.g ~ L.f : ={L.n, L.x, L.y, L.b} ==> ={L.n, L.x, L.y, L.b}.
proof. proc; fusion{1} 4!3 @ 2, 1; sim. qed.
