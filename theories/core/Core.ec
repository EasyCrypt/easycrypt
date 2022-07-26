(* -------------------------------------------------------------------- *)
lemma nosmt pw_eq ['a 'b] (x x' : 'a) (y y' : 'b):
  x = x' => y = y' => (x, y) = (x', y').
proof. by move=> -> ->. qed.

lemma nosmt pairS (x : 'a * 'b): x = (fst x, snd x).
proof. by case: x. qed.

lemma nosmt fst_pair ['a 'b] (x : 'a) (y : 'b) : fst (x, y) = x by done.
lemma nosmt snd_pair ['a 'b] (x : 'a) (y : 'b) : snd (x, y) = y by done.

(* -------------------------------------------------------------------- *)
lemma nosmt oget_none: oget None<:'a> = witness.
proof. by done. qed.

lemma nosmt oget_some (x : 'a): oget (Some x) = x.
proof. by done. qed.
hint simplify oget_some, oget_none.


lemma nosmt some_oget (x : 'a option): x <> None => x = Some (oget x).
proof. by case: x. qed.

lemma nosmt someI (x y:'a): Some x = Some y => x = y.
proof. by done. qed.

lemma nosmt none_omap ['a 'b] (f : 'a -> 'b) ox :
  omap f ox = None <=> ox = None.
proof. by case: ox. qed.

lemma oget_omap_some ['a 'b] (f : 'a -> 'b) ox :
  ox <> None => oget (omap f ox) = f (oget ox).
proof. by case: ox. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt frefl  (f     : 'a -> 'b): f == f by [].

lemma nosmt fsym   (f g   : 'a -> 'b): f == g => g == f.
proof. by move=> + x - /(_ x) ->. qed.

lemma nosmt ftrans (f g h : 'a -> 'b): f == g => g == h => f == h.
proof. by move=> + + x - /(_ x) -> /(_ x). qed.

(* -------------------------------------------------------------------- *)
lemma econgr1 ['a 'b] (f g : 'a -> 'b) x y: f == g => x = y => f x = g y.
proof. by move/fun_ext=> -> ->. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt f2refl  (f     : 'a -> 'b -> 'c): f === f by [].

lemma nosmt f2sym   (f g   : 'a -> 'b -> 'c): f === g => g === f.
proof. by move=> + x y - /(_ x y) ->. qed.

lemma nosmt f2trans (f g h : 'a -> 'b -> 'c): f === g => g === h => f === h.
proof. by move=> + + x y - /(_ x y) -> /(_ x y). qed.

lemma rel_ext (f g : 'a -> 'b -> 'c) : f = g <=> f === g.
proof.
by split=> //= fg; apply/fun_ext=> x; apply/fun_ext=> y; rewrite fg.
qed.

(* -------------------------------------------------------------------- *)
lemma eqL (x:'a): (fun y => x = y) = (=) x.
proof. by apply fun_ext. qed.

lemma eqR (y:'a): (fun x => x = y) = (=) y.
proof. by apply fun_ext=> x; rewrite (eq_sym x). qed.

(* -------------------------------------------------------------------- *)
lemma nosmt etaP (f : 'a -> 'b): eta_ f = f.
proof. by apply/fun_ext; rewrite etaE. qed.

(* -------------------------------------------------------------------- *)
lemma comp_eqE ['a 'b 'c] (f f' : 'b -> 'a) (g g' : 'c -> 'b):
  f == f' => g == g' => (f \o g) == (f' \o g').
proof. by do 2! (move/fun_ext=> ->). qed.

(* -------------------------------------------------------------------- *)
lemma nosmt can_idfun: cancel idfun<:'a> idfun<:'a>.
proof. by move => ?; rewrite /idfun. qed.

lemma nosmt can_pcan (f:'a -> 'b) g: cancel f g => pcancel f (Some \o g).
proof. by move=> fK x; rewrite /(\o) fK. qed.

lemma nosmt pcan_inj (f:'a -> 'b) g: pcancel f g => injective f.
proof. by move=> fK x y /(congr1 g); rewrite !fK. qed.

lemma nosmt can_inj (f : 'a -> 'b) g: cancel f g => injective f.
proof. by move/can_pcan/pcan_inj. qed.

lemma nosmt canLR (f:'a -> 'b) g x y: cancel f g => x = f y => g x = y.
proof. by move=> fK ->; rewrite fK. qed.

lemma nosmt canRL (f:'a -> 'b) g x y: cancel f g => f x = y => x = g y.
proof. by move=> fK <-; rewrite fK. qed.

lemma nosmt inj_eq (f : 'a -> 'b):
  injective f => forall x y, (f x = f y) <=> (x = y).
proof. by move=> inj_f x y; split=> [| -> //]; apply inj_f. qed.

lemma nosmt can_eq (f : 'a -> 'b) g:
  cancel f g => forall x y, (f x = f y) <=> (x = y).
proof. by move=> can_fg; apply inj_eq; apply (can_inj f g). qed.

lemma nosmt can2_eq (f : 'a -> 'b) g:
  cancel f g => cancel g f => forall x y, (f x = y) <=> (x = g y).
proof. by move=> fK gK x y; rewrite -{1}gK; apply (can_eq f g). qed.

(* -------------------------------------------------------------------- *)
lemma nosmt inj_idfun: injective (idfun<:'a>).
proof. by []. qed.

lemma nosmt inj_can_sym (f:'a -> 'b) f':
  cancel f f' => injective f' => cancel f' f.
proof. by move=> fK injf' x; apply injf'; rewrite fK. qed.

lemma nosmt inj_comp (f:'b -> 'a) (h:'c -> 'b):
  injective f => injective h => injective (f \o h).
proof. by move=> injf injh x y /injf /injh. qed.

lemma nosmt can_comp (f:'b -> 'a) (h:'c -> 'b) f' h':
  cancel f f' => cancel h h' => cancel (f \o h) (h' \o f').
proof. by move=> fK hK x; rewrite /(\o) fK hK. qed.

lemma nosmt pcan_pcomp (f:'b -> 'a) (h:'c -> 'b) f' h':
  pcancel f f' => pcancel h h' => pcancel (f \o h) (h' \c f').
proof. by move=> fK hK x; rewrite /(\o) /(\c) fK /= hK. qed.

lemma nosmt eq_inj (f g:'a -> 'b):
  injective f => f == g => injective g.
proof. by move=> injf eqfg x y; rewrite -2!eqfg; apply injf. qed.

lemma nosmt eq_can (f g:'a -> 'b) f' g':
  cancel f f' => f == g => f' == g' => cancel g g'.
proof. by move=> fK eqfg eqfg' x; rewrite -eqfg -eqfg' fK. qed.

lemma nosmt inj_can_eq (f g:'a -> 'b) f':
  cancel f f' => injective f' => cancel g f' => f == g.
proof. by move=> fK injf' gK x; apply injf'; rewrite fK gK. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt bij_inj (f:'b -> 'a): bijective f => injective f.
proof. by case=> g [fK _]; apply (can_inj f g). qed.

lemma nosmt bij_can_sym (f:'b -> 'a) f':
  bijective f => (cancel f' f <=> cancel f f').
proof.
move=> bij_f; have /bij_inj inj_f := bij_f.
split=> fK; 1: by apply/inj_can_sym.
by case: bij_f=> h [_ hK] x; rewrite -hK fK.
qed.

lemma nosmt bij_can_eq (f:'b -> 'a) f' f'':
  bijective f => cancel f f' => cancel f f'' => f' == f''.
proof.
move=> big_j fK fK'; apply/(inj_can_eq _ _ f);
by rewrite 1?bij_can_sym //; apply/bij_inj.
qed.

lemma bij_idfun: bijective idfun<:'a>.
proof. by exists idfun; rewrite can_idfun. qed.

lemma bij_surj (f : 'a -> 'b):
  bijective f => surjective f.
proof. by move => [g] [fgK gfK] x; exists (g x); rewrite gfK. qed.

lemma bij_inj_surj (f : 'a -> 'b):
    bijective f <=> (injective f) /\ (surjective f).
proof.
split => [bij_|[inj_ surj_]]; [by split; [apply/bij_inj|apply/bij_surj]|].
exists (fun y => choiceb (fun x => y = f x) witness); split => [x|y].
+ rewrite (eq_choice _ (pred1 x)).
  - by move => x' /=; split => [|->//]; move => /inj_ ->.
  by rewrite (choicebP (pred1 x) witness) //; exists x.
rewrite -(choicebP (fun x => y = f x) witness) //.
by case: (surj_ y) => x ->>; exists x.
qed.

(* -------------------------------------------------------------------- *)
lemma nosmt eq_bij (f:'b -> 'a):
  bijective f => forall g, f == g => bijective g.
proof.
case=> f' [fK f'K] g eqfg; exists f'; split.
by apply (eq_can f _ f'). by apply (eq_can f' _ f).
qed.

lemma nosmt bij_comp (f:'b -> 'a) (h:'c -> 'b):
  bijective f => bijective h => bijective (f \o h).
proof.
move=> [f' [fK f'K]] [h' [hK h'K]].
by exists (h' \o f'); split; apply can_comp.
qed.

lemma nosmt bij_can_bij (f:'b -> 'a):
  bijective f => forall f', cancel f f' => bijective f'.
proof. by move=> bij_f f' can_ff'; exists f; rewrite bij_can_sym. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt inv_inj (f:'a -> 'a): involutive f => injective f.
proof. by apply can_inj. qed.

lemma nosmt inv_bij (f:'a -> 'a): involutive f => bijective f.
proof. by move=> invf; exists f. qed.

lemma nosmt inv_eq ['a] (f : 'a -> 'a) :
  involutive f => forall x y, (f x = y) <=> (x = f y).
proof. by move=> fK; apply/can2_eq. qed.

(* -------------------------------------------------------------------- *)
(* Any extensional equality can be used to rewrite *)
lemma ext_rewrite (ext : 'a -> 'a -> bool) (a1 a2 : 'a) P:
   (forall x y, ext x y => x = y) => ext a1 a2 => P a1 <=> P a2.
proof. by move=> ext_eq /ext_eq ->. qed.

(* -------------------------------------------------------------------- *)
lemma pred_ext (P Q : 'a -> bool):
  P = Q <=> forall x, P x <=> Q x.
proof. by split=> //= h; apply/fun_ext=> x; rewrite h. qed.

(* -------------------------------------------------------------------- *)
pred (<=) (p q:'a -> bool) = (* subpred *)
  forall a, p a => q a.

pred (< ) (p q:'a -> bool) = (* proper *)
  p <= q /\ !(q <= p).

(* -------------------------------------------------------------------- *)
lemma nosmt subpred_eqP (p1 p2 : 'a -> bool):
  (forall x, p1 x <=> p2 x) <=> (p1 <= p2 /\ p2 <= p1).
proof.
split=> [PQ|[] + + x].
+ by split=> x /PQ.
by move=> /(_ x) + /(_ x).
qed.

lemma nosmt subpred_refl (X : 'a -> bool): X <= X
by [].

lemma nosmt subpred_asym (X Y:'a -> bool):
  X <= Y => Y <= X => X = Y.
proof. by rewrite pred_ext subpred_eqP. qed.

lemma nosmt subpred_trans (X Y Z:'a -> bool):
  X <= Y => Y <= Z => X <= Z.
proof. by move=> + + x - /(_ x) Xx /(_ x) Yx /Xx /Yx. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt pred1E (c : 'a) : pred1 c = ((=) c).
proof. by apply fun_ext=> x; rewrite (eq_sym c). qed.

lemma nosmt predU1l (x y : 'a) b : x = y => (x = y) \/ b by [].
lemma nosmt predU1r (x y : 'a) b : b => (x = y) \/ b by case: b.
lemma nosmt eqVneq (x y : 'a) : x = y \/ x <> y by case: (x = y).

lemma nosmt predT_comp ['a 'b] (p : 'a -> 'b) : predT \o p = predT by [].

lemma nosmt predUC (p1 p2 : 'a -> bool) : predU p1 p2 = predU p2 p1.
proof. by apply fun_ext=> x; rewrite /predU orbC. qed.

lemma nosmt predIC (p1 p2 : 'a -> bool) : predI p1 p2 = predI p2 p1.
proof. by apply fun_ext=> x; rewrite /predI andbC. qed.

lemma nosmt predU0 ['a] p : predU<:'a> p pred0 = p by [].

lemma nosmt pred0U ['a] p : predU<:'a> pred0 p = p by [].

lemma nosmt predIT ['a] p : predI<:'a> p predT = p by [].

lemma nosmt predTI ['a] p : predI<:'a> predT p = p by [].

lemma nosmt predCI (p : 'a -> bool) : predI (predC p) p = pred0.
proof. by apply/fun_ext=> x /=; delta => /=; rewrite andNb. qed.

lemma nosmt predCU (p : 'a -> bool) : predU (predC p) p = predT.
proof. by apply/fun_ext=> x /=; delta => /=; case: (p x). qed.

lemma nosmt predUI : right_distributive predU<:'a> predI<:'a>.
proof. by move => ???; apply/fun_ext=> x /=; delta => /=; apply/orb_andr. qed.

lemma nosmt predIU : right_distributive predI<:'a> predU<:'a>.
proof. by move=> ???; apply/fun_ext=> x /=; delta => /=; apply/andb_orr. qed.

lemma nosmt predUA : associative predU<:'a>.
proof. by move=> ???; apply/fun_ext=> x /=; delta => /=; apply/orbA. qed.

lemma nosmt predIA : associative predI<:'a>.
proof. by move=> ???; apply/fun_ext=> x /=; delta => /=; apply/andbA. qed.

lemma nosmt predUU : idempotent predU<:'a>.
proof. by move=> ?; apply/fun_ext=> x /=; delta => /=; apply/orbb. qed.

lemma nosmt predII : idempotent predI<:'a>.
proof. by move=> ?; apply/fun_ext=> x /=; delta => /=; apply/andbb. qed.

lemma nosmt subpredUl (p1 p2 : 'a -> bool):
  p1 <= predU p1 p2.
proof. by move=> x @/predU ->. qed.

lemma nosmt subpredUr (p1 p2 : 'a -> bool):
  p2 <= predU p1 p2.
proof. by move=> x @/predU ->. qed.

lemma nosmt predIsubpredl (p1 p2 : 'a -> bool):
  predI p1 p2 <= p1.
proof. by move=> x @/predI [] ->. qed.

lemma nosmt predIsubpredr (p1 p2 : 'a -> bool):
  predI p1 p2 <= p2.
proof. by move=> x @/predI [] _ ->. qed.

lemma nosmt predUsubl (p1 p2 : 'a -> bool):
  p2 <= p1 =>
  predU p1 p2 = p1.
proof. by move=> imp_; apply/fun_ext=> x /=; delta => /=; move/(_ x): imp_; case: (p1 x); case: (p2 x). qed.

lemma nosmt predUsubr (p1 p2 : 'a -> bool):
  p1 <= p2 =>
  predU p1 p2 = p2.
proof. by rewrite predUC; apply/predUsubl. qed.

lemma nosmt predIsubl (p1 p2 : 'a -> bool):
  p1 <= p2 =>
  predI p1 p2 = p1.
proof. by move=> imp_; apply/fun_ext=> x /=; delta => /=; move/(_ x): imp_; case: (p1 x); case: (p2 x). qed.

lemma nosmt predIsubr (p1 p2 : 'a -> bool):
  p2 <= p1 =>
  predI p1 p2 = p2.
proof. by rewrite predIC; apply/predIsubl. qed.

lemma nosmt predTofV (f : 'a -> 'b): predT \o f = predT.
proof. by apply/fun_ext=> x. qed.
