(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2015 - IMDEA Software Institute
 * Copyright (c) - 2012--2015 - Inria
 * 
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

op fst (p:'a * 'b): 'a = p.`1.

op snd (p:'a * 'b): 'b = p.`2.

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
  axiom mu_def (P1:'a -> bool) (P2:'b -> bool) (d1:'a distr) (d2: 'b distr):
     mu (d1 * d2) (fun p, P1 (fst p) /\ P2 (snd p)) = 
     mu d1 P1 * mu d2 P2.

  lemma mu_x_def (d1:'a distr) (d2:'b distr) p:
     mu_x (d1 * d2) p = mu_x d1 (fst p) * mu_x d2 (snd p).
  proof strict.
  do 3!rewrite /mu_x; rewrite -mu_def.
  by apply mu_eq; rewrite pred1E => x;smt.
  qed.

  lemma supp_def (d1:'a distr) (d2:'b distr) p:
    in_supp p (d1 * d2) <=>
    in_supp (fst p) d1 /\ in_supp (snd p) d2.
  proof strict.
  by do 3!rewrite /in_supp; rewrite mu_x_def; smt.
  qed.
 
  lemma weight_def (d1:'a distr) (d2:'b distr):
     weight (d1 * d2) = weight d1 * weight d2.
  proof strict.
  do 3!rewrite /weight /True; rewrite -mu_def.
  by apply mu_eq=> x.
  qed.

  lemma lossless (d1:'a distr) (d2:'b distr): 
     weight d1 = 1%r => weight d2 = 1%r =>
     weight (d1 * d2) = 1%r.
  proof strict.
  by rewrite weight_def=> -> ->.
  qed.

  lemma dprodU (d1:'a distr) (d2:'b distr): 
     is_uniform d1 => is_uniform d2 => is_uniform (d1 * d2).
  proof strict.
    move=> [Hd1_supp Hd1_suf] [Hd2_supp Hd2_suf]; split; [smt|move=> x y].
    rewrite /support !supp_def -!/(mu_x _ x) -!/(mu_x _ y) !mu_x_def /mu_x=> [Hx1 Hx2] [Hy1 Hy2].
    by rewrite (Hd1_suf (fst x) (fst y)) // (Hd2_suf (snd x) (snd y)).
  qed.

  abstract theory Sample.
    type t1.
    type t2.
    op d1 : t1 distr.
    op d2 : t2 distr.

    module S = {
      proc sample () : t1 * t2 = {
        var r;
        r = $ d1 * d2;
        return r;
      }
      proc sample2 () : t1 * t2 = {
        var r1, r2;
        r1 = $ d1;
        r2 = $ d2;
        return (r1,r2);
      }
    }.
 
    equiv sample_sample2 : S.sample ~ S.sample2 : true ==> ={res}.
    proof.
     bypr (res{1}) (res{2}) => //.
     intros &m1 &m2 a.
     cut ->: Pr[S.sample() @ &m1: a = res] = mu (d1*d2) ((=) a).
      byphoare (_: true ==> a = res)=> //.
      by proc; rnd; skip; rewrite eqL.
     apply eq_sym; cut := mu_x_def d1 d2 a. rewrite /mu_x pred1E=> ->.
     elim a=> a1 a2; rewrite /fst /snd /=.
     byphoare (_: true ==>  a1 = res.`1 /\ a2 = res.`2) => //;last by smt.
     proc; seq 1 : (a1 = r1) (mu_x d1 a1) (mu_x d2 a2) _ 0%r true => //.
       by rnd ((=) a1); auto; rewrite -(pred1E a1).
       by rnd ((=) a2); auto; rewrite -(pred1E a2).
     hoare;auto;smt.
    qed.

  end Sample.

end Dprod.

