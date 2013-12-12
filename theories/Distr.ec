require import Logic.
require export Fun.
require import Int.
require import Real.

op charfun (p:('a -> bool)) (x:'a) : real = if p x then 1%r else 0%r.

op mu_x (d:'a distr) x : real = mu d ((=) x).

op weight (d:'a distr) : real = mu d cpTrue.

op in_supp x (d:'a distr) : bool = 0%r < mu_x d x.

op support (d:'a distr) x = in_supp x d.

pred isuniform (d:'a distr) = forall (x y:'a),
  in_supp x d =>
  in_supp y d =>
  mu_x d x = mu_x d y.

(** Point-wise equality *)
pred (==)(d d':'a distr) =
  (forall x, mu_x d x = mu_x d' x).

(** Axioms *)
axiom mu_bounded (d:'a distr) (p:('a -> bool)):
  0%r <= mu d p /\ mu d p <= 1%r.

axiom mu_false (d:'a distr): mu d cpFalse = 0%r.

axiom mu_sub (d:'a distr) (p q:('a -> bool)):
  p <= q => mu d p <= mu d q.

axiom mu_supp_in (d:'a distr) p:
  mu d p = mu d cpTrue <=>
  support d <= p.

axiom pw_eq (d d':'a distr):
  d == d' => d = d'.

axiom mu_or (d:'a distr) (p q:('a -> bool)):
  mu d (cpOr p q) = mu d p + mu d q - mu d (cpAnd p q).

lemma nosmt mu_or_le (d:'a distr) (p q:('a -> bool)) r1 r2:
  mu d p <= r1 => mu d q <= r2 =>
  mu d (cpOr p q) <= r1 + r2 by [].

lemma nosmt mu_and  (d:'a distr) (p q:('a -> bool)):
  mu d (cpAnd p q) = mu d p + mu d q - mu d (cpOr p q)
by [].

lemma nosmt mu_and_le_l (d:'a distr) (p q:('a -> bool)) r:
  mu d p <= r =>
  mu d (cpAnd p q) <= r.
proof -strict.
  apply (Real.Trans _ (mu d p)).
  by (apply mu_sub;rewrite /cpAnd => x //).
qed.

lemma nosmt mu_and_le_r (d:'a distr) (p q:('a -> bool)) r :
  mu d q <= r => 
  mu d (cpAnd p q) <= r.
proof -strict.
  apply (Real.Trans _ (mu d q)).
  by (apply mu_sub;rewrite /cpAnd => x //).
qed.

(** Lemmas *)
lemma mu_supp (d:'a distr):
  mu d (support d) = mu d cpTrue.
proof strict.
by rewrite mu_supp_in.
qed.

lemma mu_eq (d:'a distr) (p q:('a -> bool)):
  p == q => mu d p = mu d q.
proof -strict.
by intros=> ext_p_q; congr=> //; apply fun_ext=> //.
qed.

lemma mu_disjoint (d:'a distr) (p q:('a -> bool)):
  (cpAnd p q <= cpFalse) =>
  mu d (cpOr p q) = mu d p + mu d q.
proof strict.
intros=> and_p_q_false;
cut inter_empty: cpAnd p q = cpFalse by apply leq_asym=> //;
by rewrite mu_or inter_empty mu_false.
qed.

lemma mu_not (d:'a distr) (p:('a -> bool)):
  mu d (cpNot p) = mu d cpTrue - mu d p.
proof strict.
cut ->: (forall (x y z:real), x = y - z <=> x + z = y) by smt;
by rewrite -mu_disjoint ?cpEM //; apply leq_refl; rewrite cpC.
qed.

lemma mu_split (d:'a distr) (p q:('a -> bool)):
  mu d p = mu d (cpAnd p q) + mu d (cpAnd p (cpNot q)).
proof strict.
rewrite -mu_disjoint; first smt.
by apply mu_eq; smt.
qed.

lemma mu_in_supp (p:('a -> bool)) (d:'a distr):
  mu d p = mu d (cpAnd p (support d)).
proof strict.
apply Antisymm; last by apply mu_sub=> x; rewrite /cpAnd.
by cut -> : (forall (p q:('a -> bool)), (cpAnd p q) = (cpNot (cpOr (cpNot p) (cpNot q))))
     by (intros=> p' q'; apply fun_ext; smt);
   rewrite mu_not mu_or !mu_not mu_supp; smt.
qed.

lemma mu_in_supp_sub (d:'a distr) (p q:('a -> bool)):
  cpAnd p (support d) <= cpAnd q (support d) =>
  mu d p <= mu d q.
proof strict.
by intros=> ple_p_q; rewrite (mu_in_supp p) (mu_in_supp q);
   apply mu_sub.
qed.

lemma mu_in_supp_eq (d:'a distr) (p q:('a -> bool)):
  cpAnd p (support d) = cpAnd q (support d) =>
  mu d p = mu d q.
proof strict.
by intros=> eq_on_supp;
   rewrite (mu_in_supp p) (mu_in_supp q);
   apply mu_eq; rewrite eq_on_supp.
qed.

lemma mu_weight_0 (d:'a distr):
  weight d = 0%r => forall p, mu d p = 0%r
by [].

lemma mu_one : forall (P : ('a -> bool))(d : 'a distr),
  P == Fun.cpTrue => 
  weight d = 1%r =>
  mu d P = 1%r.
proof -strict.
  intros => P d heq <-.
  rewrite /weight.
  congr => //.
  by apply Fun.fun_ext.
qed.  

(*** Some useful distributions *)
(** Empty distribution *)
theory Dempty.
  op dempty : 'a distr.

  axiom mu_def (p:('a -> bool)): mu dempty p = 0%r.

  lemma unique (d:'a distr):
    weight d = 0%r <=> d = dempty.
  proof -strict.
    split; last smt.
    intros weight_0; rewrite -(pw_eq<:'a> d dempty); smt.
  qed.

  lemma demptyU: isuniform dempty<:'a> by [].
end Dempty.

(** Point distribution *)
theory Dunit.
  op dunit : 'a -> 'a distr.

  axiom mu_def_in x (p:('a -> bool)):
    p x => mu (dunit x) p = 1%r.

  lemma mu_def_notin x (p:('a -> bool)):
    !p x => mu (dunit x) p = 0%r
  by [].
 
  lemma mu_x_def_eq (x:'a):
    mu_x (dunit x) x = 1%r
  by [].

  lemma mu_x_def_neq (x y:'a):
    x <> y => mu_x (dunit x) y = 0%r
  by [].

  lemma supp_def (x y:'a):
    in_supp x (dunit y) <=> x = y
  by [].

  lemma lossless (x:'a):
    weight (dunit x) = 1%r
  by [].

  lemma dunitU (x:'a):
    isuniform (dunit x)
  by [].
end Dunit.

(** Uniform distribution on (closed) integer intervals *)
theory Dinter.
  op dinter : int -> int -> int distr.

  axiom supp_def (i j x : int):
    in_supp x (dinter i j) <=> i <= x <= j.

  (* A concrete realization of this distribution using uniform
     distributions on finite sets of integers is available as
     FSet.Dinter_uni.dinter.
     Equality between the two distributions are equal, and the
     set-based definition may prove useful for computations. *)

  axiom mu_x_def_in (i j x : int):
    in_supp x (dinter i j) =>
    mu_x (dinter i j) x = 1%r / (j - i + 1)%r.

  axiom mu_x_def_notin (i j x : int):
    !in_supp x (dinter i j) => mu_x (dinter i j) x = 0%r.

  axiom weight_def (i j : int):
    weight (dinter i j) = if i <= j then 1%r else 0%r.

  lemma mu_in_supp (i j : int):
    i <= j => 
    mu (dinter i j) (fun x, i <= x <= j) = 1%r.
  proof -strict.
  by intros=> H;
     rewrite -(mu_in_supp_eq (dinter i j) cpTrue);
       try apply fun_ext;
     smt.
  qed.

  lemma isuniform (i j:int):
    isuniform (dinter i j)
  by [].
end Dinter.

(** Normalization of a sub-distribution *)
theory Dscale.
  op dscale : 'a distr -> 'a distr.

  axiom supp_def (x:'a) (d:'a distr):
    in_supp x (dscale d) <=> in_supp x d.

  axiom mu_def_0 (d:'a distr):
    weight d = 0%r =>
    forall (p:('a -> bool)), mu (dscale d) p = 0%r.

  axiom mu_def_pos (d:'a distr):
    0%r < weight d =>
    forall (p:('a -> bool)), mu (dscale d) p = mu d p / weight d.  

  lemma weight_0 (d:'a distr):
    weight d = 0%r => weight (dscale d) = 0%r
  by [].

  lemma weight_pos (d:'a distr):
    0%r < weight d => weight (dscale d) = 1%r.
  proof -strict.
  by intros=> H; rewrite /weight mu_def_pos /weight=> //; smt.
  qed.  

  lemma scaleU (d:'a distr):
    isuniform d => isuniform (dscale d)
  by [].
end Dscale.

(** Distribution resulting from applying a function to a distribution *)
theory Dapply.
  op dapply : ('a -> 'b) -> 'a distr -> 'b distr.

  axiom mu_def (d : 'a distr) (f : 'a -> 'b) P:
    mu (dapply f d) P = mu d (fun x, P (f x)).

  lemma mu_x_def (d : 'a distr) (f : 'a -> 'b) x:
    mu_x (dapply f d) x = mu d (fun y, x = f y).
  proof strict.
  by rewrite /mu_x mu_def.
  qed.

  lemma supp_def (d : 'a distr) (f : 'a -> 'b) y:
    in_supp y (dapply f d) <=> exists x, y = f x /\ in_supp x d.
  proof strict.
  rewrite /in_supp /mu_x mu_def; split.
    rewrite mu_in_supp /cpAnd /= => in_sup; smt.
    by intros=> [x]; rewrite /in_supp /mu_x=> [y_def nempty];
       cut : (=) x <= (fun x, y = f x) by (by intros=> w);
       smt.
  qed.

  lemma lossless (d : 'a distr) (f : 'a -> 'b):
    weight (dapply f d) = weight d.
  proof strict.
  by rewrite /weight mu_def /cpTrue.
  qed.
end Dapply.

(** Laplacian *) (* TODO: This is drafty! *)
theory Dlap.
  op dlap : int -> real -> int distr.

  axiom in_supp mean scale x:
    0%r <= scale => in_supp x (dlap mean scale).

(*
  axiom mu_x_def : forall (mean:int, scale:real, x:int),
    0%r <= scale => 
    mu_x (dlap mean scale) x = 
      (1%r / (2%r*scale))
    * real.exp( - (| x%r - mean%r|)) / scale. 
*)

  axiom lossless mean scale:
    0%r <= scale => weight (dlap mean scale) = 1%r.
(* x = $dlap(x1,s)   ~ x = $dlap(0,s) + x1 : ={x1,s} ==> ={x}. *)
end Dlap.
