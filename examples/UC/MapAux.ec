(*---------------------- Auxiliary Lemmas on Maps ----------------------*)

prover [""].

require import AllCore FMap FSet StdOrder.
import IntOrder.

lemma get_none (m : ('a, 'b) fmap, x : 'a) :
  x \notin m => m.[x] = None.
proof. by rewrite domE. qed.

lemma get_some (m : ('a, 'b) fmap, x : 'a) :
  x \in m => m.[x] = Some (oget m.[x]).
proof. move=> /domE; by case m.[x]. qed.

lemma set_same (m : ('a, 'b) fmap, x : 'a) :
  x \in m => m.[x <- oget m.[x]] = m.
proof.
move=> x_in_m.
apply fmap_eqP => y.
case (y = x) => [->> | ne_y_x].
by rewrite get_set_sameE get_some.
by rewrite get_setE ne_y_x.
qed.

lemma set_eq (m : ('a, 'b) fmap, x : 'a, y : 'b) :
  m.[x] = Some y => m.[x <- y] = m.
proof.
move=> m_get_x_eq_y.
have x_in_m : x \in m by rewrite domE m_get_x_eq_y.
have -> : y = oget m.[x] by rewrite m_get_x_eq_y oget_some.
by rewrite set_same.
qed.

lemma frng_set (m : ('a, 'b) fmap, x : 'a, y : 'b) :
  frng m.[x <- y] = frng (rem m x) `|` fset1 y.
proof.
apply fsetP => z; rewrite in_fsetU in_fset1 2!mem_frng 2!rngE /=.
split => [[x'] | [[x'] | ->]].
case (x' = x) => [-> | ne_x'_x].
by rewrite get_set_sameE /= => ->.
rewrite get_setE ne_x'_x /= => get_x'_some_z.
left; exists x'; by rewrite remE ne_x'_x.
rewrite remE.
case (x' = x) => // ne_x'_x get_x'_some_z.
exists x'; by rewrite get_setE ne_x'_x.
exists x; by rewrite get_set_sameE.
qed.

lemma eq_except_ne_in (x y : 'a, m1 m2 : ('a, 'b) fmap) :
  eq_except (pred1 x) m1 m2 => y <> x =>
  y \in m1 => y \in m2.
proof.
move=> /eq_exceptP @/pred1 eq_exc ne_y_x.
by rewrite 2!domE eq_exc.
qed.

lemma eq_except_setr_as_l (m1 m2 : ('a, 'b) fmap) x:
  x \in m1 => eq_except (pred1 x) m1 m2 =>
  m1 = m2.[x <- oget m1.[x]].
proof.
rewrite eq_exceptP -fmap_eqP=> x_in_m1 eqe x'.
rewrite get_setE /oget; case (x' = x)=> [->> |].
by move: x_in_m1; rewrite domE; case (m1.[x]).
by move=> ne_x'_x; rewrite eqe.
qed.

lemma eq_except_set_both x b b' (m : ('a, 'b) fmap):
  eq_except (pred1 x) m.[x <- b] m.[x <- b'].
proof. by rewrite eq_exceptP=> x'; rewrite /pred1 !get_setE=> ->. qed.

lemma eq_except_rem (m1 m2 : ('a,'b) fmap) (X : 'a -> bool) x:
   X x => eq_except X m1 m2 => eq_except X m1 (rem m2 x).
proof.
move=> X_x /eq_exceptP eq_exc; rewrite eq_exceptP=> y X_y; rewrite remE.
case (y = x)=> [->> // | ne_y_x]; by apply eq_exc.
qed.

lemma rem_id (m : ('a, 'b) fmap, x : 'a) :
  x \notin m => rem m x = m.
proof.
move=> x_notin_m; apply fmap_eqP => y; rewrite remE.
case (y = x) => // ->.
case (None = m.[x]) => // get_not_none.
rewrite eq_sym -domE // in get_not_none.
qed.

lemma map_empty (f : 'a -> 'b -> 'c) :
  map f empty = empty.
proof. by rewrite -fmap_eqP=> x; rewrite mapE 2!emptyE. qed.

lemma map_rem (f:'a -> 'b -> 'c) m x :
  map f (rem m x) = rem (map f m) x.
proof.
rewrite -fmap_eqP=> z; by rewrite !(mapE,remE); case (z = x).
qed.

lemma map_id (m:('a,'b)fmap): map (fun _ b => b) m = m.
proof. by rewrite -fmap_eqP=>x; rewrite mapE; case (m.[x]). qed.

lemma le_card_frng_fdom (m : ('a, 'b) fmap) :
  card (frng m) <= card (fdom m).
proof.
move: m.
elim /fmapW=> [| m k v k_notin_m IH].
by rewrite frng0 fdom0 2!fcards0.
rewrite mem_fdom in k_notin_m.
rewrite frng_set rem_id // fdom_set (@fcardUI_indep _ (fset1 k))
        1:fsetI1 1:mem_fdom 1:k_notin_m // fcard1 fcardU fcard1
        -addzA ler_add // -{2}(@addz0 1) ler_add // oppz_le0 fcard_ge0.
qed.

lemma fdom_frng_prop (X : 'a fset, m : ('a, 'a) fmap) :
  fdom m \proper X => frng m \subset X => frng m \proper X.
proof.
rewrite /(\proper); move=> |>.
case (frng m = X)=> // ^ eq_frng_m_X -> fdom_m_sub_X fdom_m_ne_X _.
have card_fdom_m_lt_card_X : card (fdom m) < card X.
  rewrite ltz_def; split.
  case (card X = card (fdom m))=> // /eq_sym /subset_cardP.
  by rewrite fdom_m_sub_X fdom_m_ne_X.
  by rewrite subset_leq_fcard.
have card_X_le_card_fdom_m : card X <= card (fdom m)
  by rewrite -eq_frng_m_X le_card_frng_fdom.
by rewrite /= -(@ltzz (card X)) (ler_lt_trans (card (fdom m))).
qed.

lemma fdom_frng_prop_type (m : ('a, 'a) fmap) :
  (exists (x : 'a), ! x \in m) =>
  (exists (y : 'a), ! rng m y).
proof.
move=> [x x_notin_m].
have : fdom m \proper fdom m `|` frng m `|` fset1 x.
  rewrite /(\proper); split.
  move=> z; rewrite 2!in_fsetU; move=> />.
  case (fdom m = fdom m `|` frng m `|` fset1 x)=> // contra_eq.
  rewrite -mem_fdom in x_notin_m.
  have // : x \in fdom m by rewrite contra_eq 2!in_fsetU in_fset1.
pose univ := fdom m `|` frng m `|` fset1 x.
have fdom_prop_univ frng_sub_univ : frng m \subset univ
  by move=> z @/univ; rewrite 2!in_fsetU; move=> />.
have : frng m \proper univ by apply fdom_frng_prop.
move=> /properP [_ [y [_ y_notin_frng_m]]].
rewrite mem_frng in y_notin_frng_m.
by exists y.
qed.
