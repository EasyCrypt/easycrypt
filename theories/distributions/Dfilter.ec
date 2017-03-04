(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2017 - Inria
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

require import NewLogic Int Real NewDistr FSet StdRing StdOrder StdBigop.
(*---*) import RField RealOrder Bigreal BRA.

pragma +implicits.
pragma -oldip.

(* -------------------------------------------------------------------- *)
op mfilter (m : 'a -> real) (P : 'a -> bool) (x : 'a) =
  if P x then 0%r else m x.

lemma isdistr_mfilter (m : 'a -> real) (P : 'a -> bool) :
  isdistr m =>
  isdistr (mfilter m P).
proof.
move=> [] ge0_m le1_m; split=> [x|x /le1_m {le1_m} le1_m].
+ by rewrite /mfilter; case (P x)=> //= _; exact/ge0_m.
apply/(@ler_trans (big predT m x) _ _ _ le1_m)/ler_sum=> a _.
by rewrite /mfilter fun_if2 ge0_m.
qed.

(* -------------------------------------------------------------------- *)
op dfilter (d : 'a distr) (P : 'a -> bool) = mk (mfilter (mu_x d) P).

(* -------------------------------------------------------------------- *)
lemma mux_dfilter d (P:'a -> bool) (x:'a):
  mu_x (dfilter d P) x = if P x then 0%r else mu_x d x.
proof. by rewrite muK 1:isdistr_mfilter 1:isdistr_mu_x. qed.

lemma nosmt mux_dfilter_notin (d : 'a distr) P x:
  !P x => mu_x (dfilter d P) x = mu_x d x.
proof. by rewrite mux_dfilter=> ->. qed.

lemma nosmt mux_dfilter_in d P (x:'a):
  P x => mu_x (dfilter d P) x = 0%r.
proof. by rewrite mux_dfilter=> ->. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt mu_dfilter (d : 'a distr) P E:
  mu (dfilter d P) E = mu d (predI E (predC (P))).
proof.
rewrite !muE; apply/RealSeries.eq_sum=> x /=.
by rewrite mux_dfilter /predI /predC; case: (P x).
qed.

lemma nosmt mu_dfilter_subset (d : 'a distr) P E:
  (forall x, E x => P x) =>
  mu (dfilter d P) E = 0%r.
proof.
move=> E_subset_P; rewrite mu_dfilter /predI /predC.
rewrite (@mu_eq _ _ pred0) 2:mu_false // => x @/pred0 /=.
by rewrite neqF negb_and /= -implybE; exact/E_subset_P.
qed.

lemma nosmt mu_dfilter_indep (d : 'a distr) P E:
  (forall x, !(E x /\ P x)) =>
  mu (dfilter d P) E = mu d E.
proof.
move=> E_indep_P; rewrite mu_dfilter /predI /predC.
by apply/mu_eq=> x; have:= E_indep_P x; case (E x)=> //= _ ->.
qed.

(* -------------------------------------------------------------------- *)
lemma support_dfilter ['a] (d : 'a distr) P:
  support (dfilter d P) = predI (support d) (predC P).
proof.
apply/fun_ext=> x; rewrite /support /in_supp /predI /predC mux_dfilter.
by case: (P x).
qed.

(* -------------------------------------------------------------------- *)
lemma weight_dfilter (d:'a distr) P:
  weight (dfilter d P) = weight d - mu d (P).
proof.
rewrite mu_dfilter mu_and -addrA -opprB.
by rewrite (@mu_eq _ (predU _ _) predT) // -mu_not.
qed.
