(* [proc change circuit] on a fragment inside a [while] loop: the
   fragment, the loop guard and the loop body run again on the next
   iterations, so the variables they read must be kept. *)

require import AllCore List QFABV.

type W8.

op to_bits : W8 -> bool list.
op from_bits : bool list -> W8.
op of_int : int -> W8.
op to_uint : W8 -> int.
op to_sint : W8 -> int.

bind bitstring to_bits from_bits to_uint to_sint of_int W8 8.
realize gt0_size by admit.
realize tolistP by admit.
realize oflistP by admit.
realize touintP by admit.
realize tosintP by admit.
realize ofintP by admit.
realize size_tolist by admit.

op (+^) : W8 -> W8 -> W8.
bind op W8 (+^) "xor".
realize bvxorP by admit.

op zero : W8.

(* -------------------------------------------------------------------- *)
(* The loop body before the fragment reads [x], which the fragment
   writes: [x <- x] is not a valid replacement of [x <- a]. *)
module M1 = {
  proc f(a : W8) : W8 = {
    var i : int;
    var x, y : W8;
    i <- 0;
    x <- zero;
    y <- zero;
    while (i < 2) {
      y <- x;
      x <- a;
      i <- i + 1;
    }
    return y;
  }
}.

lemma L1 : hoare [M1.f : true ==> true].
proof.
proc.
fail proc change circuit 4.2 + 1 { x <- x; }.
proc change circuit 4.2 + 1 { x <- a +^ x +^ x; }.
abort.

(* -------------------------------------------------------------------- *)
(* The fragment reads [t], which it writes on the next iterations:
   [y <- t +^ a] is not a valid replacement of [t <- t +^ a; y <- t]. *)
module M2 = {
  proc f(a : W8) : W8 = {
    var i : int;
    var t, y : W8;
    i <- 0;
    t <- zero;
    y <- zero;
    while (i < 2) {
      t <- t +^ a;
      y <- t;
      i <- i + 1;
    }
    return y;
  }
}.

lemma L2 : hoare [M2.f : true ==> true].
proof.
proc.
fail proc change circuit 4.1 + 2 { y <- t +^ a; }.
proc change circuit 4.1 + 2 { t <- a +^ t; y <- t; }.
proc change circuit [d : W8] 4.1 + 2 { d <- t; t <- a +^ d; y <- t; }.
abort.

(* -------------------------------------------------------------------- *)
(* The loop guard reads a global variable. *)
module M3 = {
  var n : int

  proc f(a : W8, b : W8) : W8 = {
    var i : int;
    var c : W8;
    i <- 0;
    c <- zero;
    while (i < n) {
      c <- a +^ b;
      i <- i + 1;
    }
    return c;
  }
}.

lemma L3 : hoare [M3.f : true ==> true].
proof.
proc.
proc change circuit 3.1 + 1 { c <- b +^ a; }.
abort.
