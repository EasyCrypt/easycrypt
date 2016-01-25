(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2016 - Inria
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)

(* In this theory, we illustrate some reasoning on distributions on
   Von Neumann's trick to simulate a fair coin toss using only a
   biased coin (of unknown bias. *)

require import Bool Int IntExtra Real RealExtra NewDistr.
require import StdRing StdOrder DBool Mu_mem.
(*---*) import RField RealOrder.

clone FixedBiased as BiasedCoin.

(* -------------------------------------------------------------------- *)
theory VonNeumann.
  import BiasedCoin.

  require import Pair FSet Dexcepted DBool.
  (*---*) import Dprod.

  module Fair = {
    proc sample(): bool = {
      var b;

      b = ${0,1};
      return b;
    }
  }.

  (* First we prove things about the distribution "pairs of uniform booleans minus pairs of identical elements" *)
  op vn = ({0,1} * {0,1}) \ (fset1 (true,true) `|` fset1 (false,false)).

  lemma pr_evict:
    mu ({0,1} * {0,1}) (mem (fset1 (true,true) `|` fset1 (false,false))) = 1%r/2%r.
  proof.
  have -> := mu_mem (fset1 (true,true) `|` fset1 (false,false)) ({0,1} * {0,1}) (inv 4%r).
  + move=> [x1 x2] _.
    rewrite (mu_eq _ _ (fun x=> (pred1 x1) (fst x) /\ (pred1 x2) (snd x))) /=.
    * by move=> [x'1 x'2]; rewrite /pred1 /fst /snd /= anda_and.
    by rewrite (Dprod.mu_def (pred1 x1) (pred1 x2)) !DBool.dboolb.
    rewrite fcardUI_indep 2:!fcard1 /= 1:fsetP=> [[x1 x2]|].
    * by rewrite !inE /=; case x1.
  smt ml=0.
  qed.

  lemma pr_final b: mu vn (pred1 (b,!b)) = 1%r/2%r.
  proof.
  rewrite -/(mu_x _ _) mux_dexcepted !inE /=.
  rewrite Dprod.weight_def DBool.dbool_predT pr_evict /=.
  rewrite mu_x_def /fst /snd /=.
  by rewrite DBool.dboolb DBool.dboolb /#.
  qed.

  lemma pr_eq b: mu vn (pred1 (b,b)) = 0%r.
  proof.
  rewrite -/(mu_x _ _) mux_dexcepted !inE /=.
  by case: b.
  qed.

  lemma support_vn a b: support vn (a,b) <=> a <> b.
  proof.
  by case: a; case: b; rewrite /support /in_supp ?pr_eq // pr_final /#.
  qed.

  lemma support_vnP: support vn = (fun (ab : bool * bool)=> ab.`1 <> ab.`2).
  proof. by rewrite pred_ext=>- [a b]; exact/support_vn. qed.

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
  have ->: Pr[Fair.sample() @ &2: b0 = res] = 1%r/2%r.
  + byphoare (_: true ==> res = b0)=> //.
    by proc; rnd (pred1 b0); skip=> /=; rewrite DBool.dboolb /#.
  byphoare (_: true ==> b0 = res)=> //.
  proc; rnd (fun (bb' : bool * bool)=> b0 = bb'.`1); skip=> /=.
  rewrite mu_support support_vnP /predI /=.
  rewrite (mu_eq _ _ (pred1 (b0,!b0))) 1:/#.
  by rewrite pr_final.
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
        b  = $dbiased;
        b' = $dbiased;
      }
      return b;
    }
  }.

  lemma Simulate_is_Fair (x:bool) &m: Pr[Simulate.sample() @ &m: res = x] = Pr[Fair.sample() @ &m: res = x].
  proof.
  have <-: Pr[SamplePair.sample() @ &m: res = x] = Pr[Fair.sample() @ &m: res = x].
  + by byequiv samplePair.
  (** The following can probably be done more cleanly by cloning WhileSampling **)
  have ->: Pr[SamplePair.sample() @ &m: res = x] = mu vn (fun (bb:bool * bool), bb.`1 = x).
  + byphoare (_: true ==> res = x)=> //.
    by proc; rnd (fun (bb:bool * bool), bb.`1 = x).
  byphoare (_: true ==> res = x)=> //.
  proc; sp.
  while true (if (b <> b') then 0 else 1) 1 (2%r * p * (1%r - p))=> //.
  + smt ml=0.
  + move=> ih.
    seq  2: true 1%r (mu vn (fun (bb:bool * bool), bb.`1 = x)) 0%r _ => //.
    * by auto=> />; rewrite dbiased_ll.
  + by auto=> />; rewrite dbiased_ll.
  + split=> //= [|z].
    * smt w=(in01_p).
  conseq (_: true ==> b <> b')=> //= />.
  seq  1: b p (1%r - p) (1%r - p) p=> //; first 3
    by rnd; skip=> />; rewrite prbiasedE /=.
  + by rnd; skip=> /> _ -> />; rewrite prbiasedE /=.
  smt w=(in01_p).
  qed.
end VonNeumann.
