require import Logic.
require import Distr.
require import Bool.
require import Real.


module M = {
  proc f (y:bool) : bool = {
    var x : bool;
    x = $Dbool.dbool; 
    return x=y;
  }
}.

lemma test: bd_hoare [ M.f : true ==> res] = (1%r/2%r).
proof.
proc.
rnd. (* (fun (x:bool), x=y). *)
skip.
simplify.
intros &hr.
rewrite (Dbool.mu_def  (fun (x : bool), x = y{hr})).
smt.
qed.

module F = {
  var b1 : bool
  var b2 : bool
  proc f () : bool = {
    b1 = $Dbool.dbool;
    b2 = $Dbool.dbool;
    return b1;
  }
}.

lemma test2: bd_hoare [ F.f : true ==> res] = (1%r/2%r). proof.
proc.
rnd;[smt|rnd; skip; smt].
qed.


require import Bitstring. 
require import Int.
op k1 : int.
op k2 : int.

module Test = {
  proc test () : bitstring = {
    var z : bitstring;
    z = $Dbitstring.dbitstring (k1+k2);
    return z;
  }

}
.

module Test' = {
  proc test () : bitstring = {
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
proc.
rnd ((=)a).
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
simplify.
smt.
trivial.
trivial.
qed.

(* not required in previous case?? *)
axiom k1_pos : 0<= k1.
axiom k2_pos : 0<= k2.

require import Array.

lemma extensionality : forall (f g : 'a -> 'b), (forall z, f z = g z) => f = g.  
smt.
qed.

lemma test'' : forall &m (a:bitstring), length a = k1+k2 => Pr[Test'.test() @ &m : a=res]=1%r/(2^(k1+k2))%r.
cut pow_distr :  ((2 ^ k2)%r * (2 ^ k1)%r = (2 ^ (k1+k2))%r).
smt.
intros &m a length_a.
bdhoare_deno (_ : (true) ==> (a=res)).
proc.
rnd (sub a 0 k1 =z1) (1%r/(2 ^ (k1))%r) (1%r/(2 ^ (k2))%r) (1%r - 1%r/(2 ^ (k1))%r) (0%r) 
    (fun z, sub a 0 k1 = z1 /\ z= (sub a k1 k2)).
simplify;rewrite -pow_distr; trivial. admit.
rnd ((=) (sub a 0 k1)).
simplify.
skip.
(* cut pow_distr :  ((2 ^ k2)%r * (2 ^ k1)%r = (2 ^ (k2+k1))%r). *) (* BUG *)
cut H : (mu_x (Dbitstring.dbitstring k1) (sub a 0 k1) = 1%r/(2^k1)%r).
rewrite (Dbitstring.mu_x_def_in k1 (sub a 0 k1) _).
smt.
smt.
generalize H; delta mu_x; simplify; intros H.
trivial.
(* *)
intros &hr h.
cut H : (mu_x (Dbitstring.dbitstring k2) (sub a k1 k2) = 1%r/(2^k2)%r).
rewrite (Dbitstring.mu_x_def_in k2 (sub a k1 k2) _).
smt.
smt.
generalize H; delta mu_x; simplify; intros H.
split.
rewrite h.
simplify.
  cut Why : ((fun (z : bool Bits.array), z = sub a k1 k2) = (=)(sub a k1 k2)) .
  delta (=).
  apply extensionality.
  simplify.
  smt.
rewrite Why.
trivial.
(* *)
intros _ v H'.
rewrite -h.
simplify.
split.
intros H3; rewrite H3.
  (* how can I use Array.sub_append_full directly?? *)
cut Again : a = sub a 0 (k1+k2) by smt.
rewrite Again.
smt.
intros Eq; rewrite Eq.
cut AndAgain : forall (xs:bitstring), (length xs = k1) => (sub (xs || v) k1 k2 = v) by smt.
rewrite AndAgain.
smt.
trivial.
admit.
(* *)
intros &hr F.
split.
cut J :  (fun z, false) = fun z, (sub a 0 k1 = z1{hr} /\ z = sub a k1 k2).
apply extensionality.
smt.
rewrite -J.
cut H :  mu ((Dbitstring.dbitstring k2))%Dbitstring
  (cpFalse) =
0%r.
apply mu_false.
smt.
smt.
trivial.
trivial.
qed.
