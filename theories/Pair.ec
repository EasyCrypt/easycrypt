op fst (p:'a * 'b): 'a = 
  let (a,b) = p in a.

op snd (p:'a * 'b): 'b = 
  let (a,b) = p in b.

lemma nosmt pw_eq (x x':'a) (y y':'b):
  x = x' => y = y' => (x,y) = (x',y')
by [].

lemma nosmt pairS (x:'a * 'b): x = (fst x,snd x)
by [].

lemma nosmt fst_pair (y:'b) (x:'a): fst (x,y) = x
by trivial.

lemma nosmt snd_pair (x:'a) (y:'b): snd (x,y) = y
by trivial.

require import Real.
require import Distr.

(* Product distribution *)
theory Dprod.
  op ( * ) : 'a distr -> 'b distr -> ('a * 'b) distr.
 
  (* This can be generalized *)
  axiom mu_def : forall P1 P2 (d1:'a distr) (d2: 'b distr),
     mu (d1 * d2) (lambda p, P1 (fst p) /\ P2 (snd p)) = 
     mu d1 P1 * mu d2 P2.

  lemma mu_x_def: forall (d1:'a distr) (d2:'b distr) p, 
     mu_x (d1 * d2) p = mu_x d1 (fst p) * mu_x d2 (snd p).
  proof.
    intros d1 d2 p;beta delta mu_x;rewrite -mu_def.
    by apply mu_eq => x;smt.
  save.

  lemma supp_def: forall (d1:'a distr) (d2:'b distr) p, 
    in_supp p (d1 * d2) <=>
    in_supp (fst p) d1 /\ in_supp (snd p) d2.
  proof.
    by intros d1 d2 p;beta delta in_supp;rewrite mu_x_def; smt.
  qed.
 
  lemma weight_def: forall (d1:'a distr) (d2:'b distr), 
     weight (d1 * d2) = weight d1 * weight d2.
  proof.
    intros d1 d2;beta delta weight cpTrue;rewrite -mu_def;apply mu_eq => x //.
  qed.

  lemma lossless (d1:'a distr) (d2:'b distr): 
     weight d1 = 1%r => weight d2 = 1%r =>
     weight (d1 * d2) = 1%r.
  proof.
    by rewrite weight_def => -> ->.
  qed.

  lemma dprodU (d1:'a distr) (d2:'b distr): 
     isuniform d1 => isuniform d2 => isuniform (d1 * d2).
  proof.
    intros Hd1 Hd2 x y; rewrite ?supp_def ?mu_x_def => [Hx1 Hx2] [Hy1 Hy2].
    by rewrite (Hd1 _ (fst y)) // (Hd2 _ (snd y)).
  save.

end Dprod.

