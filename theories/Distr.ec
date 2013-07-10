require import Logic.
require export Fun.
require import Int.
require import Real.

op charfun (p:'a cpred, x:'a) : real = if p x then 1%r else 0%r.

op mu_x(d:'a distr, x) : real = mu d ((=) x).

op weight(d:'a distr) : real = mu d cpTrue.

op in_supp (x, d:'a distr) : bool = 0%r < mu_x d x.

(** Axioms *)
axiom mu_bounded : forall (d:'a distr, p:'a cpred), 
  0%r <= mu d p /\ mu d p <= 1%r.

axiom mu_false : forall (d:'a distr), mu d cpFalse = 0%r.

axiom mu_or : forall (d:'a distr, p, q:'a cpred), 
  mu d (cpOr p q) = mu d p + mu d q - mu d (cpAnd p q).

axiom mu_in_supp : forall (d:'a distr, p:'a cpred),
  mu d p = mu d (cpAnd p (lambda x, in_supp x d)).

axiom mu_sub : forall (d:'a distr, p, q:'a cpred),
  p <= q => mu d p <= mu d q.

lemma mu_eq : forall (d:'a distr, p, q:'a cpred),
  p == q => mu d p = mu d q.
proof. smt. qed.

(* TODO : FIX this bug *)
(*lemma mu_in_supp_sub : forall (d:'a distr, p, q:'a cpred),
  (forall (a:'a), in_supp a d => p a => q a) =>
  mu d p <= mu d q.*) 

lemma mu_in_supp_sub : forall (d:'a distr, p q:'a cpred),
  (forall (a:'a), in_supp a d => p a => q a) =>
  mu d p <= mu d q.
proof.
  intros d p q H;rewrite (mu_in_supp d p).
  apply mu_sub;simplify cpAnd => x [H1 H2];apply H=> //.
save.

lemma mu_in_supp_eq : forall (d:'a distr, p q:'a cpred),
  (forall (a:'a), in_supp a d => (p a <=> q a)) =>
  mu d p = mu d q.
proof. smt. save.

(** Point-wise equality *)
pred (==)(d d':'a distr) =
  (forall x, mu_x d x = mu_x d' x).

axiom pw_eq : forall (d d':'a distr),
  d == d' <=> d = d'.

(** Lemmas *)
lemma mu_disjoint (d:'a distr) (p q:'a cpred):
  (cpAnd p q <= cpFalse) =>
  mu d (cpOr p q) = mu d p + mu d q.
proof strict.
intros=> and_p_q_false; cut inter_empty: cpAnd p q = cpFalse; first by apply leq_asym.
by rewrite mu_or inter_empty mu_false.
qed.

lemma mu_not (d:'a distr) (p:'a cpred):
  mu d (cpNot p) = mu d cpTrue - mu d p.
proof strict.
cut ->: (forall (x y z:real), x = y - z <=> x + z = y); first smt.
by rewrite -mu_disjoint ?cpEM //; apply leq_refl; rewrite cpC.
qed.

lemma mu_weight_0 : forall (d:'a distr),
  weight d = 0%r => forall p, mu d p = 0%r
by [].

(** Empty distribution *)
theory Dempty.
  op dempty : 'a distr.

  axiom mu_def : forall (p:'a cpred), mu dempty p = 0%r.

  lemma unique : forall (d:'a distr),
    weight d = 0%r <=> d = dempty.
  proof.
    intros d; split; last smt.
    intros weight_0; rewrite -(pw_eq<:'a> d dempty); smt.
  qed.
end Dempty.

(** Point distribution *)
theory Dunit.
  op dunit : 'a -> 'a distr.

  axiom mu_def_in : forall (x:'a, p:'a cpred), p x => mu (dunit x) p = 1%r.

  lemma mu_def_notin : 
    forall (x:'a, p:'a cpred), !p x => mu (dunit x) p = 0%r by [].
 
  lemma mu_x_def_eq : forall (x:'a), mu_x (dunit x) x = 1%r by [].

  lemma mu_x_def_neq : forall (x y:'a), x <> y => mu_x (dunit x) y = 0%r by [].

  lemma supp_def : forall (x y:'a), in_supp x (dunit y) <=> x = y by [].

  lemma lossless : forall (x:'a), weight (dunit x) = 1%r by [].
end Dunit.

(** FIXME/ TODO 
 * Try to express the "mu" axioms in term of mu as much as possible.
 * Then use it to prove lemma on mu_x
 * i.e as in Dunit
*)

(** Uniform distribution on (closed) integer intervals *)
theory Dinter.
  op dinter : int -> int -> int distr.

  axiom supp_def : forall (i j x:int),
    in_supp x (dinter i j) <=> i <= x <= j.

  (* We could use sums to generalize this:
  axiom mu_def : forall (i j:int) (p:int cPred),
    mu (dinter i j) p = (sum i j p)%r / (j - i + 1)%r.
  *)

  axiom mu_x_def_in : forall (i j x:int),
    in_supp x (dinter i j) =>
    mu_x (dinter i j) x = 1%r / (j - i + 1)%r.

  axiom mu_x_def_notin: forall (i j x:int),
    !in_supp x (dinter i j) => mu_x (dinter i j) x = 0%r.

  axiom weight_def : forall (i j:int), 
    weight (dinter i j) = if i <= j then 1%r else 0%r.

  
  lemma mu_in_supp : forall (i j : int),
    i <= j => 
    mu (dinter i j) (lambda x, i <= x <= j) = 1%r.
  proof.
    intros i j H.
    rewrite -(mu_in_supp_eq (dinter i j) cpTrue);smt.
  save.

end Dinter.

(** Normalization of a sub-distribution *)
theory Dscale.
  op dscale : 'a distr -> 'a distr.

  axiom supp_def : forall (d:'a distr, x:'a),
    in_supp x (dscale d) <=> in_supp x d.

  axiom mu_x_def_0: forall (d:'a distr),
    weight d = 0%r =>
    forall (p:'a cpred), mu (dscale d) p = 0%r.

  axiom mu_x_def_pos : forall (d:'a distr),
    0%r < weight d =>
    forall (p:'a cpred), mu (dscale d) p = mu d p / weight d.  

  lemma weight_0 : forall (d:'a distr),
    weight d = 0%r => weight (dscale d) = 0%r
  by [].

  lemma weight_pos : forall (d:'a distr),
    0%r < weight d => weight (dscale d) = 1%r.
  proof.
   intros d H.
   delta weight; simplify.
   rewrite (mu_x_def_pos<:'a> d _ cpTrue); first smt.
   cut ->: mu d cpTrue = weight d; smt. (* TODO: add lemmas in Real.ec to avoid unstable smt here *)
  qed.  
end Dscale.

(* Laplacian *) (* TODO: This is drafty! *)
theory Dlap.
  op dlap : int -> real -> int distr.

  axiom in_supp : forall mean scale x, 
    0%r <= scale => in_supp x (dlap mean scale).

(*
  axiom mu_x_def : forall (mean:int, scale:real, x:int),
    0%r <= scale => 
    mu_x (dlap mean scale) x = 
      (1%r / (2%r*scale))
    * real.exp( - (| x%r - mean%r|)) / scale. 
*)
  axiom lossless: forall mean scale, 
    0%r <= scale => weight (dlap mean scale) = 1%r.

(* x = $dlap(x1,s)   ~ x = $dlap(0,s) + x1 : ={x1,s} ==> ={x}. *)
end Dlap.
