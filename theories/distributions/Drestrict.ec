(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2016 - Inria
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
require import NewLogic Int Real NewDistr FSet StdRing StdOrder StdBigop.
(*---*) import RField RealOrder Bigreal BRA.

pragma +implicits.
pragma -oldip.

(* -------------------------------------------------------------------- *)
op mrestr (m : 'a -> real) (X : 'a fset) (x : 'a) =
  if mem X x then 0%r else m x.

lemma isdistr_mrestr (m : 'a -> real) (X : 'a fset) :
  isdistr m =>
  isdistr (mrestr m X).
proof.
move=> [] ge0_m le1_m; split=> [x|x /le1_m {le1_m} le1_m].
+ by rewrite /mrestr; case (mem X x)=> //= _; exact/ge0_m.
apply/(@ler_trans (big predT m x) _ _ _ le1_m)/ler_sum=> a _.
by rewrite /mrestr fun_if2 ge0_m.
qed.

op drestr (d : 'a distr) (X : 'a fset) = mk (mrestr (mu_x d) X).

lemma mux_drestr  d (X:'a fset) (x:'a):
  mu_x (drestr d X) x = if mem X x then 0%r else mu_x d x.
proof. by rewrite muK 1:isdistr_mrestr 1:isdistr_mu_x. qed.

lemma support_drestr ['a] (d : 'a distr) X:
  support (drestr d X) = predI (support d) (predC (mem X)).
proof.
apply/fun_ext=> x; rewrite /support /in_supp /predI /predC mux_drestr.
by case: (mem X x).
qed.

lemma nosmt mux_drestr_notin (d : 'a distr) X x:
  !mem X x => mu_x (drestr d X) x = mu_x d x.
proof. by rewrite mux_drestr=> ->. qed.

lemma nosmt mux_drestr_in d X (x:'a):
  mem X x => mu_x (drestr d X) x = 0%r.
proof. by rewrite mux_drestr=> ->. qed.

lemma nosmt mu_drestr (d : 'a distr) X E:
  mu (drestr d X) E = mu d (predI E (predC (mem X))).
proof.
rewrite !muE; apply/RealSeries.eq_sum=> x /=.
by rewrite mux_drestr /predI /predC; case: (mem X x).
qed.

lemma nosmt mu_drestr_subset (d : 'a distr) X E:
  (forall x, E x => mem X x) =>
  mu (drestr d X) E = 0%r.
proof.
move=> E_subset_X; rewrite mu_drestr /predI /predC.
rewrite (@mu_eq _ _ pred0) 2:mu_false // => x @/pred0 /=.
by rewrite neqF negb_and /= -implybE; exact/E_subset_X.
qed.

lemma weight_drestr (d:'a distr) X:
  weight (drestr d X) = weight d - mu d (mem X).
proof.
rewrite mu_drestr mu_and -addrA -opprB.
by rewrite (@mu_eq _ (predU _ _) predT) // -mu_not.
qed.
