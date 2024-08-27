(* -------------------------------------------------------------------- *)
require import AllCore List FSet FMap Distr.
require import Ring Number StdRing StdOrder.
(*---*) import RField RealOrder.

lemma mu_mem_le_gen (s:'a fset) (d:'b distr) p (bd:real) : 
  (forall (x : 'a), mem s x => mu d (p x) <= bd) =>
  mu d (fun r => exists x, x \in s /\ p x r) <= (card s)%r * bd.
proof.
elim/fset_ind: s; first by rewrite mu0_false; smt(in_fset0 fcards0).
move => x s x_fresh IH H. 
rewrite (@mu_eq _ _ (predU (p x)
  (fun (r : 'b) => exists (x : 'a), (x \in s) /\ p x r))); 1: smt(in_fsetU1).
rewrite mu_or; apply ler_naddr; 1: smt(mu_bounded).
by rewrite fcardU1 x_fresh fromintD mulrDl /b2i /=; smt(in_fsetU1).
qed.

lemma mu_mem_le (s:'a fset): forall (d:'a distr) (bd:real),
  (forall (x : 'a), mem s x => mu d (pred1 x) <= bd) =>
  mu d (mem s) <= (card s)%r * bd.
proof. 
by move => d bd; have X := mu_mem_le_gen s d pred1 bd; smt(mu_eq).
qed.

(* NOTE: In order to generalize mu_mem_ge in the same way as mu_mem_le
above, we would need to assume disjointness of the sets [p x], so we
don't do this here for now *)

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
    by have := mu_bound x _=> //; smt(mu_bounded).
  move: (x::l) mu_bound=> {x l} l mu_bound.
  apply (ler_trans ((card (oflist l))%r * bd)).
    exact/(mu_mem_le_card l d bd mu_bound).
  rewrite cardE -(perm_eq_size (undup l)) 1:oflistK //.
  by rewrite ler_wpmul2r // le_fromint size_undup.
qed.

lemma mu_mem_le_fsize (m : ('a, 'b) fmap) (d : 'c distr) p bd :
  (forall u, u \in m => mu d (p u) <= bd) =>
  mu d (fun r => exists u, u \in m /\ p u r) <= (fsize m)%r * bd.
proof.
elim/fmapW : m; first by rewrite mu0_false; smt(mem_empty fsize_empty).
move => m k v fresh_k IH H.
rewrite (@mu_eq _ _ (predU (p k)
  (fun (r : 'c) => exists (u : 'a), (u \in m) /\ p u r))); 1: smt(mem_set).
rewrite mu_or; apply ler_naddr; 1: smt(mu_bounded).
by rewrite fsize_set -mem_fdom fresh_k fromintD mulrDl; smt(mem_set).
qed.
