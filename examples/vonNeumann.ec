(* In this theory, we illustrate some reasoning on distributions on
   Von Nuemann's trick to simulate a fair coin toss using only a
   biased coin (of unknown bias. *)

require import Bool.
require import Real.
require import Distr.

theory BiasedCoin.
  op p:real.
  axiom p_bnd: 0%r < p < 1%r.

  op biased: bool distr.

  axiom biased_def (P:bool -> bool):
    mu biased P =
      p         * charfun P true +
      (1%r - p) * charfun P false.

  lemma biased_full: support biased = True.
  proof.
    apply fun_ext=> b; rewrite /True /support /in_supp /mu_x.
    by case b; rewrite biased_def /charfun /Pred.([!]) /=; smt.
  qed.
  
  lemma biasedL: mu biased True = 1%r.
  proof. by rewrite biased_def /True /charfun /=; smt. qed.
end BiasedCoin.

theory VonNeumann.
  import BiasedCoin.
  require import Pred.
  require import Pair.
  (*---*) import Dprod.
  require import FSet.
  (*---*) import Dexcepted.

  module Fair = {
    proc sample(): bool = {
      var b;

      b = ${0,1};
      return b;
    }
  }.

  (* First we prove things about the distribution "pairs of uniform booleans minus pairs of identical elements" *)
  op vn = ({0,1} * {0,1}) \ (add (true,true) (add (false,false) empty)).

  lemma mux_vn_TF: mu vn ((=) (true,false)) = 1%r/2%r.
  proof.
    rewrite -/(mu_x _ _) /vn mu_x_def.
    cut ->: in_supp (true,false) ({0,1} * {0,1} \ add (true,true) (add (false,false) empty)).
      cut [_ H]:= supp_def (true,false) ({0,1} * {0,1}) (add (true,true) (add (false,false) empty)).
      by apply H; split; smt.
    rewrite /=.
    cut ->: weight ({0,1} * {0,1}) = 1%r by smt.
    cut ->: cpMem (add (true,true) (add (false,false) empty)) = (((=) (true,true)) \/ ((=) (false,false))).
      by rewrite /cpMem /Pred.(\/) -fun_ext=> x; smt.
    rewrite mu_disjoint; first smt.
    cut split_eq: forall (a b:bool), ((=) (a,b)) = fun x, (fun x, a = x) (fst x) /\ (fun x, b = x) (snd x).
      by move=> a b; rewrite -fun_ext; smt.
    rewrite !split_eq.
    rewrite !Dprod.mu_def.
    cut eq_eta: forall (b:bool), (fun x, b = x) = ((=) b).
      by move=> b; rewrite -fun_ext=> x.
    rewrite !eq_eta -/(mu_x _ _) -/(mu_x _ _) Dprod.mu_x_def /fst/ snd /= !Dbool.mu_x_def.
    smt.
  qed.

  lemma mux_vn_FT: mu vn ((=) (false,true)) = 1%r/2%r.
  proof.
    rewrite -/(mu_x _ _) /vn mu_x_def.
    cut ->: in_supp (false,true) ({0,1} * {0,1} \ add (true,true) (add (false,false) empty)).
      cut [_ H]:= supp_def (false,true) ({0,1} * {0,1}) (add (true,true) (add (false,false) empty)).
      apply H; split.
        smt.
        by rewrite !mem_add -!nor; do !(split; last smt); smt.
    rewrite /=.
    cut ->: weight ({0,1} * {0,1}) = 1%r by smt.
    cut ->: cpMem (add (true,true) (add (false,false) empty)) = (((=) (true,true)) \/ ((=) (false,false))).
      by rewrite /cpMem /Pred.(\/) -fun_ext=> x /=; rewrite !mem_add; smt.
    rewrite mu_disjoint; first smt.
    cut split_eq: forall (a b:bool), ((=) (a,b)) = fun x, (fun x, a = x) (fst x) /\ (fun x, b = x) (snd x).
      by move=> a b; rewrite -fun_ext; smt.
    rewrite !split_eq.
    rewrite !Dprod.mu_def.
    cut eq_eta: forall (b:bool), (fun x, b = x) = ((=) b).
      by move=> b; rewrite -fun_ext=> x.
    rewrite !eq_eta -/(mu_x _ _) -/(mu_x _ _) Dprod.mu_x_def /fst/ snd /= !Dbool.mu_x_def.
    smt.
  qed.

  lemma supp_vn a b:
    in_supp (a,b) vn <=>
    a <> b.
  proof.
    rewrite /vn; split.
      move=> H.
      cut [H1 _]:= supp_def (a,b) ({0,1} * {0,1}) (add (true,true) (add (false,false) empty)).
      apply H1 in H; move: H=> [_].
      by rewrite !mem_add -!nor; smt.
      move=> neq_a_b.
      cut [_ H]:= supp_def (a,b) ({0,1} * {0,1}) (add (true,true) (add (false,false) empty)).
      apply H; split; first smt.
      rewrite !mem_add -!nor; smt.
  qed.

  module SamplePair = {
    proc sample(): bool = {
      var b, b';

      (b,b') = $vn;
      return b;
    }
  }.

  equiv samplePair: SamplePair.sample ~ Fair.sample: true ==> ={res}.
  proof.
    bypr (res{1}) (res{2})=> // &1 &2 b0.
    cut ->: Pr[Fair.sample() @ &2: b0 = res] = 1%r/2%r.
      byphoare (_: true ==> res = b0)=> //.
      by proc; rnd ((=) b0); skip; progress; smt.
    byphoare (_: true ==> b0 = res)=> //.
    proc; rnd (fun bb', let (b,b') = bb' in b0 = b); skip; progress.
      rewrite mu_support.
      cut ->: ((fun bb', let (b,b') = bb' in b0 = b) /\ support vn) = ((=) (b0,!b0)).
        rewrite -fun_ext /Pred.(/\) /support=> bb' /=.
        by elim/tuple2_ind bb'=> bb' b b' bb'_def /=; smt.
      by case b0=> /=; [rewrite mux_vn_TF | rewrite mux_vn_FT].
      by move: H0 H1; elim/tuple2_ind v.
  qed.

  (* We can now prove that sampling a pair in the restricted
     distribution and flipping two coins independently until
     they are distinct, returning the first one, are equivalent *)
  module Simulate = {
    proc sample(): bool = {
      var b, b';

      b  = true;
      b' = true;
      while (b = b') {
        b  = $biased;
        b' = $biased;
      }
      return b;
    }
  }.
end VonNeumann.