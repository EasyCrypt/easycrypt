require import Logic.
require import Distr.
require import Bool.
require import Real.



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
phoare_deno (_ : (true) ==> (a=res)); [|trivial|trivial].
proc.
rnd ((=)a);skip;smt.
qed.


(* not required in previous case?? *)
axiom k1_pos : 0<= k1.
axiom k2_pos : 0<= k2.


require import Fun.

axiom mu_neg : forall (d:'a distr, p:'a cpred), 
  mu d (Fun.cpNot p) = mu d (Fun.cpTrue) - mu d p .

lemma test'' : forall &m (a:bitstring), length a = k1+k2 => Pr[Test'.test() @ &m : a=res]=1%r/(2^(k1+k2))%r.
intros &m a length_a.
phoare_deno (_ : (true) ==> (a=res));[|trivial|trivial].
proc.
rnd (z1=sub a 0 k1) (1%r/(2 ^ (k1))%r) (1%r/(2 ^ (k2))%r) (1%r-1%r/(2 ^ (k1))%r) (0%r) (fun z, z1=sub a 0 k1 /\ z=sub a k1 k2).
smt.
rnd; skip; progress.
cut H : (mu_x (Dbitstring.dbitstring k1) (sub a 0 k1) = 1%r/(2^k1)%r).
apply (Dbitstring.mu_x_def_in k1 (sub a 0 k1) _).
smt.
rewrite - H.
delta mu_x.
simplify.
cut -> : (fun (x : bitstring), x = sub a 0 k1) = ((=) (sub a 0 k1));[apply Fun.fun_ext; smt|trivial].
(* rnd (1%r/(2 ^ (k1))%r) (=sub a 0 k1). *)
(* simplify. *)
(* cut pow_distr :  ((2 ^ k2)%r * (2 ^ k1)%r = (2 ^ (k1+k2))%r). *)
(* smt. *)
(* rewrite <- pow_distr. *)
(* cut test :  (forall (x:real), x<>0%r => x/x = 1%r). *)
(* smt. *)
(* smt. *)
intros &hr J.
split.
cut H: (mu_x (Dbitstring.dbitstring k2) (sub a k1 k2) = 1%r/(2^k2)%r);
    [apply (Dbitstring.mu_x_def_in k2 (sub a k1 k2) _);smt|].
cut -> :  (fun (z : bool array), z1{hr} = sub a 0 k1 /\ z = sub a k1 k2) =  (fun (z : bool array), z = sub a k1 k2);
    [apply Fun.fun_ext; smt|].
generalize H; delta mu_x; beta; intros H.
cut -> : (fun (z : bool array), z = sub a k1 k2) = ((=) (sub a k1 k2)); [apply Fun.fun_ext;smt|].
rewrite - H. trivial.
intros H.
intros v _.
split.
intros G.
cut -> : v = sub a k1 k2; [smt|].
cut -> : z1{hr} = sub a 0 k1; [smt|].
rewrite - {1} (sub_append_full a). 
rewrite length_a.
smt.
intros.
intros G.
simplify.
split.
smt.
smt.
(********)
rnd; skip; progress; try smt.

cut -> : (fun (x : bitstring), ! x = sub a 0 k1) = (Fun.cpNot ( (=) (sub a 0 k1) )).
apply fun_ext. smt.
rewrite mu_neg.
cut -> : (mu ((Dbitstring.dbitstring k1))%Dbitstring (Fun.cpTrue)) = 1%r.
smt.
cut H : (mu_x (Dbitstring.dbitstring k1) (sub a 0 k1) = 1%r/(2^k1)%r).
apply (Dbitstring.mu_x_def_in k1 (sub a 0 k1) _).
smt.
generalize H; delta mu_x; simplify; intros H.
rewrite H.
trivial.
(*****)
smt.
qed.


lemma test : forall (a:bitstring), length a = k1+k2 => equiv [ Test.test ~ Test'.test : true ==> ={res}]. 
intros a h.
bypr (res{1}) (res{2}).
smt.
intros a0 &m1 &m2 _.
rewrite  (test' &m1 a0 _); [admit |].
rewrite  (test'' &m2 a0 _); [admit |].
trivial.
qed.




