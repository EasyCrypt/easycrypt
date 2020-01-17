require import Int.
(* require import CHoareTactic. *)

module A = { 
  proc g (x, y) : int = {
    var r : int;
    r <- x + y;
    r <- r * x;
    return r * r;
  }

  proc f (x : int) : int = {
    var a : int;
    a <- x + 1;
    a <@ g(a,x);
  return a;
  }
}.

lemma silly : choare[A.g : true ==> true] time [3].
proof.
proc.
wp =>//.
qed.

lemma silly2 : choare[A.g : true ==> true] time [2].
proof.
proc.
wp.
skip.
(* We ran out of time. *)
admit. 
qed.

lemma silly3 : choare[A.f : true ==> true] time [7].
proof.
proc.
call silly.
(* Alternatively, we can do: *)
(* call (_: true ==> true time [3]). *)
(* apply silly. *)
wp =>//.
qed.

module B = { 
  proc f (x, y) : int = {
    var r : int;
    if (y < x) {
      r <- 1;
      r <- 1;
     } else {
      r <- 2;
      r <- 2;
    }
    return r;
  }
}.

(* For if statements, we add the cost of both branches. *)
lemma silly4 : choare[B.f : true ==> true] time [6].
proof.
proc.
wp=>//.
qed.

module C = { 
  proc f (x, y) : int = {
    while (x < y) {
      x <- x + 1;
    }
    return x;
  }
}.

lemma silly5 : forall (x,y : int), 
    choare[C.f : x < y ==> true] time [2 * (x - y) + 1].
proof.
move => x y.
proc.
while (x <= y) x (x - y) [fun _ => 1].
