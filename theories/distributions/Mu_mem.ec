(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
require import AllCore List FSet Distr.
require import Ring Number StdRing StdOrder.
(*---*) import RField RealOrder.

lemma mu_mem_le (s:'a fset): forall (d:'a distr) (bd:real),
  (forall (x : 'a), mem s x => mu d (pred1 x) <= bd) =>
  mu d (mem s) <= (card s)%r * bd.
proof.
  elim/fset_ind s=> [d bd mu_bound|x s x_notin_s ih d bd mu_bound].
    by rewrite (mu_eq d _ pred0) 2:mu0 2:fcards0 // => x; rewrite inE.
  rewrite fcardUI_indep 1:fsetP 2:fcard1.
    by move=> x0; rewrite !inE; split=> [[h ->>]|].
  rewrite addzC fromintD mulrDl /=.
  rewrite (mu_eq d _ (predU (pred1 x) (mem s))).
    by move=> z; rewrite !inE orbC.
  rewrite mu_disjoint.
    by rewrite /predI /pred1 /pred0=> z [->].
  rewrite ler_add 1:mu_bound // 1:!inE //.
  by apply ih=> z z_in_s; rewrite mu_bound // !inE; left.
qed.

lemma mu_mem_ge (s:'a fset): forall (d:'a distr) (bd:real),
  (forall (x : 'a), mem s x => mu d (pred1 x) >= bd) =>
  mu d (mem s) >= (card s)%r * bd.
proof.
  elim/fset_ind s=> [d bd mu_bound|x s x_notin_s ih d bd mu_bound].
    by rewrite (mu_eq d _ pred0) 2:mu0 2:fcards0 // => x; rewrite inE.
  rewrite fcardUI_indep 1:fsetP 2:fcard1.
    by move=> x0; rewrite !inE; split=> [[h ->>]|].
  rewrite addzC fromintD mulrDl /=.
  rewrite (mu_eq d _ (predU (pred1 x) (mem s))).
    by move=> z; rewrite !inE orbC.
  rewrite mu_disjoint.
    by rewrite /predI /pred1 /pred0=> z [->].
  rewrite ler_add 1:mu_bound // 1:!inE //.
  by apply ih=> z z_in_s; rewrite mu_bound // !inE; left.
qed.

lemma mu_mem (s:'a fset): forall (d:'a distr) (bd:real),
  (forall (x : 'a), mem s x => mu d (pred1 x) = bd) =>
  mu d (mem s) = (card s)%r * bd.
proof.
  move=> d bd mu_cnst; rewrite eqr_le; split => [|_].
    by apply mu_mem_le=> x h; rewrite mu_cnst.
  by apply mu_mem_ge=> x h; rewrite mu_cnst // -le_ge.
qed.

lemma mu_mem_card (l:'a list) (d:'a distr) (bd:real):
  (forall (x : 'a), mem l x => mu d (pred1 x) = bd) =>
  mu d (mem l) = (card (oflist l))%r * bd.
proof.
  move=> mu_cnst; rewrite (mu_eq _ _ (mem (oflist l))).
    by move=> x; rewrite mem_oflist.
  by apply mu_mem=> x; rewrite mem_oflist=> /mu_cnst.
qed.

lemma mu_mem_le_card (l:'a list) (d:'a distr) (bd:real):
  (forall (x : 'a), mem l x => mu d (pred1 x) <= bd) =>
  mu d (mem l) <= (card (oflist l))%r * bd.
proof.
  move=> mu_bound; rewrite (mu_eq _ _ (mem (oflist l))).
    by move=> x; rewrite mem_oflist.
  by apply mu_mem_le=> x; rewrite mem_oflist=> /mu_bound.
qed.

lemma mu_mem_ge_card (l:'a list) (d:'a distr) (bd:real):
  (forall (x : 'a), mem l x => mu d (pred1 x) >= bd) =>
  mu d (mem l) >= (card (oflist l))%r * bd.
proof.
  move=> mu_bound; rewrite (mu_eq _ _ (mem (oflist l))).
    by move=> x; rewrite mem_oflist.
  by apply mu_mem_ge=> x; rewrite mem_oflist=> /mu_bound.
qed.

lemma mu_mem_le_size (l:'a list) (d:'a distr) (bd:real):
  (forall (x : 'a), mem l x => mu d (pred1 x) <= bd) =>
  mu d (mem l) <= (size l)%r * bd.
proof.
  case l=> [//=|x l mu_bound].
    by rewrite (mu_eq _ _ pred0) // mu0.
  have le0_mu: 0%r <= bd.
    by have := mu_bound x _=> //; smt.
  move: (x::l) mu_bound=> {x l} l mu_bound.
  apply (ler_trans ((card (oflist l))%r * bd)).
    exact/(mu_mem_le_card l d bd mu_bound).
  rewrite cardE -(perm_eq_size (undup l)) 1:oflistK //.
  by rewrite ler_wpmul2r // le_fromint size_undup.
qed.
