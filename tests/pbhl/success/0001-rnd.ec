require import Logic.
require import Distr.
require import Bool.
require import Real.


module M = {
  fun f (y:bool) : bool = {
    var x : bool;
    x = $Dbool.dbool; 
    return x=y;
  }
}.

lemma test: bd_hoare [ M.f : true ==> res] = (1%r/2%r).
proof.
fun.
rnd (1%r/2%r) (lambda (x:bool), x=y).
skip.
trivial.
simplify.
intros &hr.
rewrite (Dbool.mu_def  (lambda (x : bool), x = y{hr})).
smt.
save.

module F = {
  var b1 : bool
  var b2 : bool
  fun f () : bool = {
    b1 = $Dbool.dbool;
    b2 = $Dbool.dbool;
    return b1;
  }
}.

lemma test2: bd_hoare [ F.f : true ==> res] = (1%r/2%r). proof.
fun.
rnd (1%r) (lambda (x:bool), true).
rnd (1%r/2%r) (lambda (x:bool), x).
skip.
(* <<<<<<< HEAD *)
trivial.
simplify.
rewrite (Dbool.mu_def  (lambda (x : bool), true)).
rewrite (Dbool.mu_def  (lambda (x : bool), x)).
split.
trivial.
intros H v H'.
split.
trivial.
trivial.
save.



require import Bitstring. 
require import Int.
op k1 : int.
op k2 : int.

module Test = {
  fun test () : bitstring = {
    var z : bitstring;
    z = $Dbitstring.dbitstring (k1+k2);
    return z;
  }

}
.

module Test' = {
  fun test () : bitstring = {
    var z1 : bitstring;
    var z2 : bitstring;
    z1 = $Dbitstring.dbitstring (k1);
    z2 = $Dbitstring.dbitstring (k2);
    return z1||z2;
  }

}
.

lemma test' : forall &m (a:bitstring), length a = k1+k2 => Pr[Test.test() @ &m : a=res]=1%r/(2^(k1+k2))%r.
intros &m a length_a.
bdhoare_deno (_ : (true) ==> (a=res)).
fun.
rnd (1%r/(2 ^ (k1 + k2))%r) (lambda (z:bitstring), a=z).
skip.
trivial.
simplify.
(* rewrite (Dbitstring.mu_x_def_in (k1+k2) a _). *)
(* trivial. *)
cut H : (mu_x (Dbitstring.dbitstring (k1+k2)) a = 1%r/(2^(k1+k2))%r).
apply (Dbitstring.mu_x_def_in (k1+k2) a _).
assumption.
generalize H.
delta mu_x.
delta cPeq.
simplify.
intros H1.
apply H1.
trivial.
trivial.
(* ======= *)
smt.
(* >>>>>>> 8d6399d16b9a22a735b5d0027bd9f51eee968177 *)
save.

(* not required in previous case?? *)
axiom k1_pos : 0<= k1.
axiom k2_pos : 0<= k2.


lemma test'' : forall &m (a:bitstring), length a = k1+k2 => Pr[Test'.test() @ &m : a=res]=1%r/(2^(k1+k2))%r.
intros &m a length_a.
bdhoare_deno (_ : (true) ==> (a=res)).
fun.
rnd (1%r/(2 ^ (k2))%r) (lambda (z:bitstring), sub a k1 k2 =z).
rnd (1%r/(2 ^ (k1))%r) (lambda (z:bitstring), sub a 0 k1 =z).
simplify.
skip.
(* cut pow_distr :  ((2 ^ k2)%r * (2 ^ k1)%r = (2 ^ (k2+k1))%r). *) (* BUG *)
cut pow_distr :  ((2 ^ k2)%r * (2 ^ k1)%r = (2 ^ (k1+k2))%r).
trivial.
rewrite pow_distr.
cut test :  (forall (x:real), x<>0%r => x/x = 1%r).
trivial.
trivial.
intros &hr _.
split.
cut H : (mu_x (Dbitstring.dbitstring k1) (sub a 0 k1) = 1%r/(2^k1)%r).
apply (Dbitstring.mu_x_def_in k1 (sub a 0 k1) _).
trivial.
assumption.
intros _ v v_in_supp.
split.
intros Hv.
split.

cut H : (mu_x (Dbitstring.dbitstring k2) (sub a k1 k2) = 1%r/(2^k2)%r).
apply (Dbitstring.mu_x_def_in k2 (sub a k1 k2) _).
trivial.
assumption.
intros _ v0 v0_in_supp.
split.
intros H.
rewrite -H.
rewrite -Hv.

cut Trivial : (sub a k1 k2 = sub a (0+k1) k2).
trivial.
rewrite Trivial.
rewrite (sub_append_sub<:bool> a 0 k1 k2 _ _ _ _ ).
trivial.
trivial.
trivial.
trivial.
rewrite -length_a.
rewrite (sub_append_full<:bool> a). 
split.
intros H.
rewrite H.
trivial.
intros H'.
cut H'' : (
      (sub a k1 k2 = (sub a k1 k2) => a = (v || sub a k1 k2))).
trivial.
rewrite (H'' _).
trivial.
trivial.
trivial.
trivial.
save.
