require import Logic.
require import Distr.
require import Bool.
require import Real.



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
rnd (1%r/(2 ^ (k1 + k2))%r) (=a).
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
save.

(* not required in previous case?? *)
axiom k1_pos : 0<= k1.
axiom k2_pos : 0<= k2.


lemma test'' : forall &m (a:bitstring), length a = k1+k2 => Pr[Test'.test() @ &m : a=res]=1%r/(2^(k1+k2))%r.
intros &m a length_a.
bdhoare_deno (_ : (true) ==> (a=res)).
fun.
rnd (1%r/(2 ^ (k2))%r) (=sub a k1 k2).
rnd (1%r/(2 ^ (k1))%r) (=sub a 0 k1).
simplify.
skip.
(* cut pow_distr :  ((2 ^ k2)%r * (2 ^ k1)%r = (2 ^ (k2+k1))%r). *) (* BUG *)
cut pow_distr :  ((2 ^ k2)%r * (2 ^ k1)%r = (2 ^ (k1+k2))%r).
smt.
rewrite pow_distr.
cut test :  (forall (x:real), x<>0%r => x/x = 1%r).
smt.
smt.
intros &hr _.
split.
cut H : (mu_x (Dbitstring.dbitstring k1) (sub a 0 k1) = 1%r/(2^k1)%r).
apply (Dbitstring.mu_x_def_in k1 (sub a 0 k1) _).
smt.
rewrite <- H.
delta mu_x.
simplify.
trivial.
intros _ v v_in_supp.
split.
intros Hv.
split.

cut H : (mu_x (Dbitstring.dbitstring k2) (sub a k1 k2) = 1%r/(2^k2)%r).
apply (Dbitstring.mu_x_def_in k2 (sub a k1 k2) _).
smt.
(* rewrite <- H. delta. simplify. trivial. *)
assumption. (* BUG?? *)
intros _ v0 v0_in_supp.
split.
intros H.
rewrite <- H.
rewrite <- Hv.

cut Trivial : (sub a k1 k2 = sub a (0+k1) k2).
smt.
rewrite Trivial.
rewrite (sub_append_sub<:bool> a 0 k1 k2 _ _ _ _ ).
smt.
smt.
smt.
smt.
rewrite <- length_a.
rewrite (sub_append_full<:bool> a). 
split.
intros H.
rewrite H.
smt.
intros H'.
cut H'' : (
      (sub a k1 k2 = (sub a k1 k2) => a = (v || sub a k1 k2))).
smt.
rewrite (H'' _).
smt.
smt.
trivial.
trivial.
save.


lemma test : forall (a:bitstring), length a = k1+k2 => equiv [ Test.test ~ Test'.test : true ==> ={res}]. 
intros a h.
bypr (a=res{1}) (a=res{2}).
trivial.
intros &m1 &m2 _.
rewrite  (test' &m1 a _); [assumption |].
rewrite  (test'' &m2 a _); [assumption |].
trivial.
save.


