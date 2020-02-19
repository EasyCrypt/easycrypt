require import Int List CHoareTactic StdBigop.
import Bigint IntExtra.

schema plus_cost ['a] {e e' : int}: 
cost[true : e + e'] = 
cost[true : e] + cost[true : e'] + 1 .
print plus_cost.

lemma foo : cost(_:{})[true : 1 + 2] = 1.
proof.
instantiate := (plus_cost {} 1 : 2) => H; rewrite H.
have := a.
admit.
qed.

lemma bar : 
cost(_ : {z : int})[z = 1 : z + 2] = 1.
proof.



(*****************)
(* Example BR93: *)
(*****************)
module type Oracle = {
  proc o (x : int) : int
}.

op k1 : int.
op k2 : int.

axiom k1p : 0 <= k1.
axiom k2p : 0 <= k2.

module type Adv (H : Oracle) = {
  proc a1(x : int) : int * int
  proc a2(x : int) : int
}.

(*****************)
(* Other example *)

(* We have two possibility to give module restrictions. *)
(* We can give the restrictions function by function, e.g.: *)
module type OAdv (H1 : Oracle) (H : Oracle) = {
  proc a1(x : int) : int * int {H.o : k1, H1.o : 1} 
  proc a2(x : int) : int       {H.o : k2, H1.o : 3} 
}.

(* Or we can  give the restrictions at the top-level, e.g.: *)
module type OAdvBis (H1 : Oracle, H : Oracle) 
  [a1 : {H.o, H1.o; H.o : k1, H1.o : 1 },
   a2 : {H.o, H1.o; H.o : k2, H1.o : 3 }]
 = {
  proc a1(x : int) : int * int
  
  proc a2(x : int) : int
}.
(*****************)

(* Inverter *)
module I (A : Adv) (H : Oracle) = {
  var qs : int list

  module QRO = {
    proc o (x : int) = {
      var r : int;
      qs <- x :: qs;
      r <- H.o(x);
      return r;
    }
  }
  module A0 = A(QRO)

  proc invert(pk : int, y : int) : int = {
    var m0,m1,b,x : int;

    qs <- [];
    (m0,m1) <- A0.a1(pk);    
    b <- A0.a2(y);
    x <- nth witness qs (find (fun _ => true) qs);
    return  x;
  }
}.

section.
  declare module H : Oracle {-I}. 
  declare module A : Adv {-I, -H} [a1 : {#H.o : k1}, a2 : {#H.o : k2}].

  local module I0 = I(A,H).

  local lemma bound_i :     
    choare[I0.invert: true ==> true] 
    time [3 + 2 * k1 + 2 * k2; I(A,H).A0.a1 : 1; I(A,H).A0.a2 : 1; H.o : k1 + k2].
  proof.
  proc.
  seq 3 : (size I.qs <= k1 + k2) [k1 + k2].
  call (_: true ;
    (I(A, H).QRO.o : size I.qs - k1)
    time
    (I(A, H).QRO.o : [fun _ => 1; H.o : fun _ => 1]))
  => * /=.
  (* We prove that the invariant is preserved by calls to the oracle QRO. *)
  proc.
  call (_: true; time).
  wp; skip => *. 
  split => /=; [1: by smt].
  admit.
  call (_: true;
    (I(A, H).QRO.o : size I.qs)
    time
    (I(A, H).QRO.o : [fun _ => 1; H.o : fun _ => 1]))
  => * /=.
  (* We prove that the invariant is preserved by calls to the oracle QRO. *)
  proc; call (_: true; time); wp; skip => *.
  split; [1: by smt].
  split; [2: by smt].
  admit.
  wp; skip => *.
  split => * /=; [1: by smt].
  split;
  rewrite !big_constz !count_predT !size_range [smt (k1p k2p)].
  (* wp (size I.qs <= k1 + k2). *)  
  admit.
qed.

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
wp; skip => *; split => //.
admit.
qed.

lemma silly3 : choare[A.f : true ==> true] time [4].
proof.
proc.
call silly.
(* Alternatively, we can do: *)
(* call (_: true ==> true time [1]). *)
(* apply silly. *)
wp; skip => *; split =>//.
admit.
qed.

module B = { 
  proc f (x, y) : int = {
    var r : int;
    if (y < x) {
      r <- 1 + 1;
      r <- 1 + 1;
     } else {
      r <- 2 + 1;
      r <- 2 + 1;
    }
    return r;
  }
}.

(* For if statements, we add the cost of both branches. *)
lemma silly4 : choare[B.f : true ==> true] time [5].
proof.
proc.
wp; skip => *; split => //.
admit.
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
0 <= a /\ 0 <= b =>
choare[C.f : x = a /\ y = b /\ x < y ==> true] time [2 * (a - b) + 1].
proof.
move => a b p => /=.
proc.
(* - invariant, 
   - increasing quantity starting from zero
   - number of loop iterations
   - cost of one loop body. *)
while (x <= y /\ y = b) (x - a) (b - a) [fun _ => 1] => *.

(* prove that the loop body preserves the invariant, and cost what was stated. *)
wp; skip => * /=.
split; [1: by smt].
admit.

(* prove that the invariant and loop condition implies that we have not reached 
  the maximal number of steps.  *)
by smt.

(* we prove that the invariant implies the post, and that the cost of all
 iterations is smaller than the final cost. *)
skip => * => //; split; [1: by smt].
rewrite !big_constz !count_predT !size_range. 
print list_ind.
admit.
qed.
