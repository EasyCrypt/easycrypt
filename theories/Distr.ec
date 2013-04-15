require import Logic.
require export Fun.
require import Int.
require import Real.

op caract (p:'a cPred, x : 'a) : real = 
   if p x then 1%r else 0%r.

(** Core axioms and definitions on mu *)
axiom mu_bounded: forall (d:'a distr) (P:'a cPred), 
  0%r <= mu d P && mu d P <= 1%r .

axiom mu_false: forall (d:'a distr),
  mu d cPfalse = 0%r. 

axiom mu_incl: forall P1 P2 (d:'a distr),
  cPincl P1 P2 => mu d P1 <= mu d P2.

op mu_weight(d:'a distr): real = mu d cPtrue.

op mu_x(d:'a distr, x): real = mu d (cPeq x).

(** Support *)
op in_supp (x, d:'a distr): bool = mu_x d x <> 0%r.

(** Lemmas *)
lemma mu_weight_0 : forall (d:'a distr),
  (mu_weight d = 0%r => forall P, mu d P = 0%r) /\
  ((forall P, mu d P = 0%r) => mu_weight d = 0 %r)
proof.
intros d;split.
  intros H P;cut upper_bound: (mu d P <= mu d cPtrue);
  [ apply (mu_incl<:'a> P cPtrue d _);trivial |
    trivial ].
  trivial.
save.

(* Unit Distribution *)
theory Dunit.
  op dunit: 'a -> 'a distr.

  axiom mu_def_in: forall x (P:'a cPred),
    P x => mu (dunit x) P = 1%r.

  axiom mu_def_notin: forall x (P:'a cPred), 
    !P x => mu (dunit x) P = 0%r.

  lemma mu_x_def_eq: forall (x:'a),
    mu_x (dunit x) x = 1%r.

  lemma mu_x_def_neq: forall (x y:'a),
    x <> y => mu_x (dunit x) y = 0%r.

  lemma supp_def: forall (x1 x2:'a), 
    in_supp x1 (dunit x2) <=> x1 = x2.

  lemma mu_weight: forall (x:'a),
     mu_weight (dunit x) = 1%r.
end Dunit.

(** FIXME/ TODO 
 * Try to express the "mu" axioms in term of mu as much as possible.
 * Then use it to prove lemma on mu_x
 * i.e as in Dunit
*)

(* Uniform distribution on (closed) integer intervals *)
theory Dinter.
  op dinter: int -> int -> int distr.

  axiom supp_def: forall i j x,
    in_supp x (dinter i j) <=> i <= x /\ x <= j.

  axiom mu_x_def_in: forall i j x,
    in_supp x (dinter i j) =>
    mu_x (dinter i j) x = 1%r / (i - j + 1)%r.

  axiom mu_x_def_nin: forall (i j x:int),
    !in_supp x (dinter i j) =>  mu_x (dinter i j) x = 0%r.

  axiom mu_weight_le: forall (i j:int), i <= j =>
    mu_weight (dinter i j) = 1%r.
 
  axiom mu_weight_gt: forall (i j:int), j < i =>
    mu_weight (dinter i j) = 0%r.
end Dinter.

(* Normalization of a sub-distribution *)
theory Dscale.
  op dscale: 'a distr -> 'a distr.

  axiom supp_def: forall (d:'a distr) x,
    in_supp x (dscale d) <=> in_supp x d.

  axiom mu_x_def_0: forall (d:'a distr, x:'a),
    mu_weight d = 0%r => 
    mu_x (dscale d) x = 0%r.

  axiom mu_x_def_diff: forall (d:'a distr, x:'a),
    mu_weight d <> 0%r =>
    mu_x (dscale d) x = mu_x d x / mu_weight d.  

  axiom mu_weight_0 : forall (d:'a distr),
    mu_weight d = 0%r => 
    mu_weight (dscale d) = 0%r.

  axiom mu_weight_1 : forall (d:'a distr),
    mu_weight d <> 0%r => 
    mu_weight (dscale d) = 1%r.
end Dscale.

(* Laplacian *) (* TODO: This is drafty! *)
theory Dlap.
  op dlap: int -> real -> int distr.

  axiom in_supp: forall mean scale x, 
    0%r <= scale => in_supp x (dlap mean scale).

(*
  axiom mu_x_def : forall (mean:int, scale:real, x:int),
    0%r <= scale => 
    mu_x (dlap mean scale) x = 
      (1%r / (2%r*scale))
    * real.exp( -! (| x%r - mean%r|)) / scale. 
*)
  axiom mu_weight: forall mean scale, 
    0%r <= scale => mu_weight (dlap mean scale) = 1%r.

(* x = $dlap(x1,s)   ~ x = $dlap(0,s) + x1 : ={x1,s} ==> ={x}. *)
end Dlap.
