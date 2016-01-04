(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2016 - Inria
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* Parts of this API have been imported from the [ssrfun] library of
 * the ssreflect library that is (c) Copyright Microsoft Corporation
 * and Inria. *)

(* -------------------------------------------------------------------- *)
require import ExtEq Option.

(* -------------------------------------------------------------------- *)
op idfun ['a] (x:'a) = x.

(* -------------------------------------------------------------------- *)
pred preim ['a 'b] (f : 'a -> 'b) p x = p (f x).

(* -------------------------------------------------------------------- *)
abbrev transpose ['a 'b 'c] (f : 'a -> 'b -> 'c) (y : 'b) = fun x=> f x y.

(* -------------------------------------------------------------------- *)
op eta_ (f : 'a -> 'b) = fun x => f x
  axiomatized by etaE.

lemma nosmt etaP (f : 'a -> 'b): eta_ f = f.
proof. by apply/fun_ext; rewrite etaE. qed.

(* -------------------------------------------------------------------- *)
op (\o) ['a 'b 'c] (g : 'b -> 'c) (f : 'a -> 'b) =
  fun x => g (f x).

op (\c) ['a 'b 'c] (f : 'b -> 'a option) (g : 'c -> 'b option) =
  fun x => obind f (g x).

(* -------------------------------------------------------------------- *)
lemma comp_eqE ['a 'b 'c] (f f' : 'b -> 'a) (g g' : 'c -> 'b):
  f == f' => g == g' => (f \o g) == (f' \o g').
proof. by do 2! (move/fun_ext=> ->). qed.

(* -------------------------------------------------------------------- *)
pred morphism_1 (f : 'a -> 'b) aF rF =
  forall x, f (aF x) = rF (f x).

pred morphism_2 (f : 'a -> 'b) aOp rOp =
  forall x y, f (aOp x y) = rOp (f x) (f y).

pred homomorphism_1 (f : 'a -> 'b) aP rP =
  forall x, aP x => rP (f x).

pred homomorphism_2 (f : 'a -> 'b) aR rR =
  forall x y, aR x y => rR (f x) (f y).

pred monomorphism_1 (f : 'a -> 'b) (aP : 'a -> 'c) rP =
  forall x, rP (f x) = aP x.

pred monomorphism_2 (f : 'a -> 'b) (aR : 'a -> 'a -> 'c) rR =
  forall x y, rR (f x) (f y) = aR x y.

(* -------------------------------------------------------------------- *)
 pred injective (f : 'a -> 'b) =
   forall x y, f x = f y => x = y.

 pred cancel (f : 'a -> 'b) (g : 'b -> 'a) =
   forall x, g (f x) = x.

 pred pcancel (f : 'a -> 'b) (g : 'b -> 'a option) =
   forall x, g (f x) = Some x.

 pred ocancel (g : 'b -> 'a option) h =
   forall x, oapp h x (g x) = x.

(* -------------------------------------------------------------------- *)
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
pred bijective ['a 'b] (f : 'b -> 'a) = exists g, cancel f g /\ cancel g f.

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
pred involutive (f:'a -> 'a) = cancel f f.

lemma nosmt inv_inj (f:'a -> 'a): involutive f => injective f.
proof. by apply can_inj. qed.

lemma nosmt inv_bij (f:'a -> 'a): involutive f => bijective f.
proof. by move=> invf; exists f. qed.

lemma nosmt inv_eq ['a] (f : 'a -> 'a) :
  involutive f => forall x y, (f x = y) <=> (x = f y).
proof. by move=> fK; apply/can2_eq. qed.

(* -------------------------------------------------------------------- *)
pred left_inverse (e:'a) (inv:'a -> 'a) (o:'a -> 'a -> 'a) =
  forall (x:'a), o (inv x) x = e.

pred right_inverse (e:'a) (inv:'a -> 'a) (o:'a -> 'a -> 'a) =
  forall (x:'a), o x (inv x) = e.

pred left_inverse_in (p : 'a -> bool) (e : 'a) inv (o : 'a -> 'a -> 'a) =
  forall x, p x => o (inv x) x = e.

pred right_inverse_in (p : 'a -> bool) (e : 'a) inv (o : 'a -> 'a -> 'a) =
  forall x, p x => o x (inv x) = e.

pred left_injective (o:'a -> 'a -> 'a) =
  forall (x y z:'a), o y x = o z x => y = z.

pred right_injective (o:'a -> 'a -> 'a) =
  forall (x y z:'a), o x y = o x z => y = z.

pred left_injective_in p (o:'a -> 'a -> 'a) =
  forall x, p x => forall y z, o y x = o z x => y = z.

pred right_injective_in p (o:'a -> 'a -> 'a) =
  forall x, p x => forall y z, o x y = o x z => y = z.

pred right_id e (o:'a -> 'b -> 'a) =
  forall x, o x e = x.

pred left_zero z (o:'a -> 'b -> 'a) =
  forall x, o z x = z.

pred right_commutative (o:'a -> 'b -> 'a) =
  forall x y z, o (o x y) z = o (o x z) y.

pred left_distributive (o1:'a -> 'b -> 'a) (o2:'a -> 'a -> 'a) =
  forall x y z, o1 (o2 x y) z = o2 (o1 x z) (o1 y z).

pred right_loop (inv : 'b -> 'b) (o:'a -> 'b -> 'a) =
  forall y, cancel (fun x, o x y) (fun x, o x (inv y)).

pred rev_right_loop inv (o:'a -> 'b -> 'a) =
  forall y, cancel (fun x, o x (inv y)) (fun x, o x y).

pred left_loop inv (o:'a -> 'b -> 'b) =
  forall x, cancel (o x) (o (inv x)).

pred rev_left_loop inv (o:'a -> 'b -> 'b) =
  forall x, cancel (o (inv x)) (o x).

pred right_loop_in p (inv : 'b -> 'b) (o:'a -> 'b -> 'a) =
  forall y, p y => cancel (fun x, o x y) (fun x, o x (inv y)).

pred rev_right_loop_in p inv (o:'a -> 'b -> 'a) =
  forall y, p y => cancel (fun x, o x (inv y)) (fun x, o x y).

pred left_loop_in p inv (o:'a -> 'b -> 'b) =
  forall x, p x => cancel (o x) (o (inv x)).

pred rev_left_loop_in p inv (o:'a -> 'b -> 'b) =
  forall x, p x => cancel (o (inv x)) (o x).

pred left_id e (o:'a -> 'b -> 'b) =
  forall x, o e x = x.

pred right_zero z (o:'a -> 'b -> 'b) =
  forall x, o x z = z.

pred left_commutative (o:'a -> 'b -> 'b) =
  forall x y z, o x (o y z) = o y (o x z).

pred right_distributive (o:'a -> 'b -> 'b) add =
  forall x y z, o x (add y z) = add (o x y) (o x z).

pred self_inverse e (o:'a -> 'a -> 'b) =
 forall x, o x x = e.

pred commutative (o:'a -> 'a -> 'b) =
  forall x y, o x y = o y x.

pred idempotent (o:'a -> 'a -> 'a) =
  forall x, o x x = x.

pred associative (o:'a -> 'a -> 'a) =
  forall x y z, o x (o y z) = o (o x y) z.

pred interchange op1 op2 =
  forall (x:'a) y z t, op1 (op2 x y) (op2 z t) = op2 (op1 x z) (op1 y t).

(* -------------------------------------------------------------------- *)
(* Any extensional equality can be used to rewrite *)
lemma ext_rewrite (ext : 'a -> 'a -> bool) (a1 a2 : 'a) P:
     (forall x y, ext x y => x = y) (* subrel ext (=) *)
  => ext a1 a2
  => P a1 <=> P a2.
proof. by move=> ext_eq /ext_eq ->. qed.
