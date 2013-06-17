require import Logic.
require export Fun.
require import Int.
require import Real.

op charfun (p:'a cPred, x:'a) : real = if p x then 1%r else 0%r.

op mu_x(d:'a distr, x) : real = mu d (cPeq x).

op weight(d:'a distr) : real = mu d cPtrue.

op in_supp (x, d:'a distr) : bool = 0%r < mu_x d x.

(** Axioms *)
axiom mu_bounded : forall (d:'a distr, p:'a cPred), 
  0%r <= mu d p /\ mu d p <= 1%r.

axiom mu_false : forall (d:'a distr), mu d cPfalse = 0%r.

axiom mu_or : forall (d:'a distr, p, q:'a cPred), 
  mu d (cPor p q) = mu d p + mu d q - mu d (cPand p q).

axiom mu_sub : forall (d:'a distr, p, q:'a cPred), p <= q => mu d p <= mu d q.

(** Lemmas *)
lemma mu_disjoint : forall (d:'a distr, p, q:'a cPred),
  (cPand p q <= cPfalse) => mu d (cPor p q) = mu d p + mu d q
by [].

lemma mu_not : forall (d:'a distr, p:'a cPred), 
  mu d (cPnot p) = mu d cPtrue - mu d p.
proof.
  intros d p.
  cut H: (forall (x y z:real), x + z = y => x = y - z); [smt | ].
  apply (H (mu d (cPnot p)) (mu d cPtrue) (mu d p) _).
  cut H1: (mu d cPtrue = mu d (cPor (cPnot p) p)); smt.
qed.

lemma mu_weight_0 : forall (d:'a distr),
  weight d = 0%r => forall p, mu d p = 0%r
by [].

(** Point distribution *)
theory Dunit.
  op dunit : 'a -> 'a distr.

  axiom mu_def_in : forall (x:'a, p:'a cPred), p x => mu (dunit x) p = 1%r.

  lemma mu_def_notin : 
    forall (x:'a, p:'a cPred), !p x => mu (dunit x) p = 0%r by [].
 
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
    in_supp x (dinter i j) <=> i <= x /\ x <= j.

  (* We could use sums to generalize this:
  axiom mu_x_def : forall (i j:int) (p:int cPred),
    mu (dinter i j) p = (sum i j p)%r / (j - i + 1)%r.
  *)

  axiom mu_x_def_in : forall (i j x:int),
    in_supp x (dinter i j) =>
    mu_x (dinter i j) x = 1%r / (j - i + 1)%r.

  axiom mu_x_def_notin: forall (i j x:int),
    !in_supp x (dinter i j) => mu_x (dinter i j) x = 0%r.

  axiom weight_def : forall (i j:int), 
    weight (dinter i j) = if i <= j then 1%r else 0%r.
end Dinter.

(** Normalization of a sub-distribution *)
theory Dscale.
  op dscale : 'a distr -> 'a distr.

  axiom supp_def : forall (d:'a distr, x:'a),
    in_supp x (dscale d) <=> in_supp x d.

  axiom mu_x_def_0: forall (d:'a distr),
    weight d = 0%r =>
    forall (p:'a cPred), mu (dscale d) p = 0%r.

  axiom mu_x_def_pos : forall (d:'a distr),
    0%r < weight d =>
    forall (p:'a cPred), mu (dscale d) p = mu d p / weight d.  

  lemma weight_0 : forall (d:'a distr),
    weight d = 0%r => weight (dscale d) = 0%r
  by [].

  lemma weight_pos : forall (d:'a distr),
    0%r < weight d => weight (dscale d) = 1%r.
  proof.
   intros d H.
   delta weight; simplify.
   rewrite (mu_x_def_pos<:'a> d _ cPtrue); smt.
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
    * real.exp( -! (| x%r - mean%r|)) / scale. 
*)
  axiom lossless: forall mean scale, 
    0%r <= scale => weight (dlap mean scale) = 1%r.

(* x = $dlap(x1,s)   ~ x = $dlap(0,s) + x1 : ={x1,s} ==> ={x}. *)
end Dlap.
