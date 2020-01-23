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

  var g : int

  proc f (x, y) : int = {
    while (x < y) {
      x <- x + 1;
    }
    return x;
  }
}.

lemma silly5 : forall (a : int) (b : int), 
choare[C.f : x = a /\ y = b /\ x < y ==> true] time [2 * (a - b) + 1].
proof.
move => a b.
proc.
(* - invariant, 
   - increasing quantity starting from zero
   - number of loop iterations
   - cost of one loop body. *)
while (x <= y /\ y = b) (x - a) (b - a) [fun _ => 1]. 

(* prove that the loop body preserves the invariant, and cost what was stated. *)
move => z; wp; skip => //.
move => &hr=> hyp => //.
split => /=. by smt.
admit.

(* prove that the invariant and loop condition implies that we have not reached 
  the maximal number of steps.  *)
move => &hr.  by smt.

(* we prove that the invariant implies the post, and that the cost of all
 iterations is smaller than the final cost. *)
skip => &hr hyp => /=.
split. by smt.
admit.
qed.
