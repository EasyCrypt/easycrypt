(* -------------------------------------------------------------------- *)
(* [kill] inside a while loop: the killed code must write nothing read
   by the loop guard or by the loop body (the part before the killed
   code included), as they run again on the next iterations. *)
require import AllCore.

module M = {
  proc f() : int = {
    var i, x, y : int;
    i <- 0;
    x <- 0;
    y <- 0;
    while (i < 2) {
      y <- x;
      x <- x + 1;
      i <- i + 1;
    }
    return y;
  }
}.

lemma M_f : hoare [M.f : true ==> res = 1].
proof.
proc.
unroll 4; rcondt 4; 1: by auto.
unroll 7; rcondt 7; 1: by auto.
rcondf 10; 1: by auto.
by auto.
qed.

(* [x] is read at the start of the next iteration: [kill] is rejected,
   otherwise the judgement below, that contradicts [M_f] (and [f]
   terminates), would be provable. *)
lemma kill_body_head : phoare [M.f : true ==> res = 0] = 1%r.
proof.
proc.
fail kill 4.2.
abort.

(* Same, the killed code spanning the end of the loop body. *)
lemma kill_body_end : hoare [M.f : true ==> true].
proof.
proc.
fail kill 4.2 ! 2.
fail kill 4.2 ! *.
abort.

(* [i] is read by the loop guard. *)
lemma kill_guard : hoare [M.f : true ==> true].
proof.
proc.
fail kill 4.3.
abort.

(* -------------------------------------------------------------------- *)
module N = {
  proc f() : int = {
    var i, j, x, y, z : int;
    i <- 0;
    x <- 0;
    y <- 0;
    z <- 0;
    while (i < 2) {
      y <- x;
      j <- 0;
      while (j < 1) {
        if (i = 0) {
          x <- x + 1;
          z <- z + 1;
        }
        j <- j + 1;
      }
      i <- i + 1;
    }
    return y;
  }
}.

(* Nested loops and conditionals: [x] is read by the outer loop body. *)
lemma kill_nested : hoare [N.f : true ==> true].
proof.
proc.
fail kill 5.3.1.1.
fail kill 5.3.1.1 ! *.
fail kill 5.3.
abort.

(* [z] is read by no code that may run after: [kill] applies. *)
lemma kill_nested_ok : hoare [N.f : true ==> true].
proof.
proc.
kill 5.3.1.2; 1: by auto.
kill 5.1; 1: by auto.
abort.

(* -------------------------------------------------------------------- *)
(* Legitimate uses: the killed variables are read before the loop only,
   or before the conditional only. *)
module O = {
  proc f() : int = {
    var i, x, y : int;
    i <- 0;
    x <- 0;
    y <- x;
    while (i < 2) {
      x <- i;
      i <- i + 1;
    }
    if (y = 0) {
      x <- 1;
    }
    return y;
  }
}.

lemma kill_ok : hoare [O.f : true ==> res = 0].
proof.
proc.
kill 4.1; 1: by auto.
kill 5.1; 1: by auto.
wp; while (y = 0); 1: by auto.
by auto.
qed.
