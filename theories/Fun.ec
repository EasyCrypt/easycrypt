(* --------------------------------------------------------------------
 * Copyright IMDEA Software Institute / INRIA - 2013, 2014
 * -------------------------------------------------------------------- *)

(* Parts of this API have been imported from the [seq] library of
 * the ssreflect library that is (c) Copyright Microsoft Corporation
 * and Inria. *)

require import ExtEq.
require import Option.

(*** Properties of functions (see ssrfun) *)
(** Definitions *)
(* id<:'a> is the identity function on 'a *)
op id (x:'a) = x.

(* preim f p x <=> x is in the preimage of p by f *)
pred preim ['a 'b] (f : 'a -> 'b) p x = p (f x).

(** Definitions for composition *)
theory Composition.
  op comp (g:'b -> 'c) (f:'a -> 'b): ('a -> 'c) =
    fun x, g (f x).

  op pcomp (f:'b -> 'a option) (g:'c -> 'b option) x =
    obind f (g x).

  lemma eq_comp (f:'b -> 'a) f' (g:'c -> 'b) g':
    f == f' =>
    g == g' =>
    comp f g == comp f' g'.
  proof. by move=> eq_ff' eq_gg' x; rewrite /comp eq_gg' eq_ff'. qed.
end Composition.
export Composition.

theory Morphism.
  (** Morphisms *)
  (* Morphism property for unary and binary functions *)
  pred morphism_1 (f:'a -> 'b) aF rF =
    forall x, f (aF x) = rF (f x).

  pred morphism_2 (f:'a -> 'b) aOp rOp =
    forall x y, f (aOp x y) = rOp (f x) (f y).

  (* Homomorphism property for unary and binary relations *)
  pred homomorphism_1 (f:'a -> 'b) aP rP =
    forall x, aP x => rP (f x).

  pred homomorphism_2 (f:'a -> 'b) aR rR =
    forall x y, aR x y => rR (f x) (f y).

  (* Stability property for unary and binary relations *)
  pred monomorphism_1 (f:'a -> 'b) (aP: 'a -> 'c) rP =
    forall x, rP (f x) = aP x.

  pred monomorphism_2 (f:'a -> 'b) (aR:'a -> 'a -> 'c) rR =
    forall x y, rR (f x) (f y) = aR x y.
end Morphism.
export Morphism.

theory Injections.
  pred injective (f:'a -> 'b) =
    forall (x y:'a), f x = f y => x = y.

  pred cancel (f:'a -> 'b) (g:'b -> 'a) =
    forall x, g (f x) = x.

  pred pcancel (f:'a -> 'b) (g:'b -> 'a option) =
    forall x, g (f x) = Some x.

  pred ocancel (g:'b -> 'a option) h =
    forall x, oapp h x (g x) = x.

  lemma nosmt can_pcan (f:'a -> 'b) g: cancel f g => pcancel f (fun y, Some (g y)).
  proof. by move=> fK x //=; congr; rewrite fK. qed.

  lemma nosmt pcan_inj (f:'a -> 'b) g: pcancel f g => injective f.
  proof.
    move=> fK x y h; apply (congr1 g) in h.
    by generalize h; rewrite !fK; apply someI.
  qed.

  lemma nosmt can_inj (f : 'a -> 'b) g: cancel f g => injective f.
  proof. by move=> h; apply can_pcan in h; apply pcan_inj in h. qed.

  lemma nosmt canLR (f:'a -> 'b) g x y: cancel f g => x = f y => g x = y.
  proof. by move=> fK ->; rewrite fK. qed.

  lemma nosmt canRL (f:'a -> 'b) g x y: cancel f g => f x = y => x = g y.
  proof. by move=> fK <-; rewrite fK. qed.
end Injections.
export Injections.

theory InjectionsTheory.
  lemma nosmt inj_id: injective (id<:'a>).
  proof. by []. qed.

  lemma nosmt inj_can_sym (f:'a -> 'b) f': cancel f f' => injective f' => cancel f' f.
  proof. by move=> fK injf' x; apply injf'; rewrite fK. qed.

  lemma nosmt inj_comp (f:'b -> 'a) (h:'c -> 'b): injective f => injective h => injective (comp f h).
  proof. by move=> injf injh x y hy; apply injf in hy; apply injh. qed.

  lemma nosmt can_comp (f:'b -> 'a) (h:'c -> 'b) f' h':
    cancel f f' => cancel h h' => cancel (comp f h) (comp h' f').
  proof. by move=> fK hK x; rewrite /comp /comp fK hK. qed.

  lemma nosmt pcan_pcomp (f:'b -> 'a) (h:'c -> 'b) f' h':
    pcancel f f' => pcancel h h' => pcancel (comp f h) (pcomp h' f').
  proof. by move=> fK hK x; rewrite /comp /pcomp fK /= hK. qed.

  lemma nosmt eq_inj (f g:'a -> 'b): injective f => f == g => injective g.
  proof. by move=> injf eqfg x y; rewrite -2!eqfg; apply injf. qed.

  lemma nosmt eq_can (f g:'a -> 'b) f' g': cancel f f' => f == g => f' == g' => cancel g g'.
  proof. by move=> fK eqfg eqfg' x; rewrite -eqfg -eqfg' fK. qed.

  lemma nosmt inj_can_eq (f g:'a -> 'b) f': cancel f f' => injective f' => cancel g f' => f == g.
  proof. by move=> fK injf' gK x; apply injf'; rewrite fK gK. qed.
end InjectionsTheory.
export InjectionsTheory.

theory Bijections.
  pred bijective (f:'b -> 'a) = exists g,
    cancel f g /\ cancel g f.

  lemma nosmt bij_inj (f:'b -> 'a): bijective f => injective f.
  proof. by case=> g [fK _]; apply (can_inj f g). qed.

  lemma nosmt bij_can_sym (f:'b -> 'a) f': bijective f => (cancel f' f <=> cancel f f').
  proof.
    intros=> bijf; split=> fK; first by apply inj_can_sym; [apply fK | apply bij_inj].
    by case bijf=> h [_ hK] x; rewrite -hK fK.
  qed.

  lemma nosmt bij_can_eq (f:'b -> 'a) f' f'': bijective f => cancel f f' => cancel f f'' => f' == f''.
  proof.
    move=> bijf.
    rewrite -bij_can_sym // => fK.
    rewrite -bij_can_sym // => fK'.
    by apply (inj_can_eq f' f'' f)=> //; apply bij_inj.
  qed.
end Bijections.
export Bijections.

theory BijectionsTheory.
  lemma nosmt eq_bij (f:'b -> 'a): bijective f => forall g, f == g => bijective g.
  proof.
    case=> f' [fK f'K] g eqfg; exists f'; split.
      by apply (eq_can f _ f').
      by apply (eq_can f' _ f).
  qed.

  lemma nosmt bij_comp (f:'b -> 'a) (h:'c -> 'b): bijective f => bijective h => bijective (comp f h).
  proof.
  by move=> [f' [fK f'K]] [h' [hK h'K]]; exists (comp h' f'); split; apply can_comp.
  qed.

  lemma nosmt bij_can_bij (f:'b -> 'a): bijective f => forall f', cancel f f' => bijective f'.
  proof.
    case=> f' [fK f'K] g gK.
    cut eqf'g:= bij_can_eq f f' g _ _ _=> //; first by exists f'.
    by exists f; split; [apply (eq_can f' _ f) | apply (eq_can f _ f')].
  qed.
end BijectionsTheory.
export BijectionsTheory.

theory Involutions.
  pred involutive (f:'a -> 'a) = cancel f f.

  lemma nosmt inv_inj (f:'a -> 'a): involutive f => injective f.
  proof. by apply can_inj. qed.

  lemma nosmt inv_bij (f:'a -> 'a): involutive f => bijective f.
  proof. by move=> invf; exists f. qed.
end Involutions.
export Involutions.

theory OperationProperties.
  theory SopTisR.
    pred left_inverse (e:'a) (inv:'a -> 'a) (o:'a -> 'a -> 'a) =
      forall (x:'a), o (inv x) x = e.

    pred right_inverse (e:'a) (inv:'a -> 'a) (o:'a -> 'a -> 'a) =
      forall (x:'a), o x (inv x) = e.  

    pred left_injective (o:'a -> 'a -> 'a) =
      forall (x y z:'a), o x y = o z y => x = z.

    pred right_injective (o:'a -> 'a -> 'a) =
      forall (x y z:'a), o x y = o x z => y = z.
  end SopTisR.
  export SopTisR.

  theory SopTisS.
    pred right_id e (o:'a -> 'b -> 'a) =
      forall x, o x e = x.

    pred left_zero z (o:'a -> 'b -> 'a) =
      forall x, o z x = z.

    pred right_commutative (o:'a -> 'b -> 'a) =
      forall x y z, o (o x y) z = o (o x z) y.

    pred left_distributive (o1:'a -> 'b -> 'a) (o2:'a -> 'a -> 'a) =
      forall x y z, o1 (o2 x y) z = o2 (o1 x z) (o1 y z).

    pred right_loop inv (o:'a -> 'b -> 'a) =
      forall y, cancel (fun x, o x y) (fun x, o x (inv y)).

    pred rev_right_loop inv (o:'a -> 'b -> 'a) =
      forall y, cancel (fun x, o x (inv y)) (fun x, o x y).
  end SopTisS.
  export SopTisS.

  theory SopTisT.
    pred left_id e (o:'a -> 'b -> 'b) =
      forall x, o e x = x.

    pred right_zero z (o:'a -> 'b -> 'b) =
      forall x, o x z = z.

    pred left_commutative (o:'a -> 'b -> 'b) =
      forall x y z, o x (o y z) = o y (o x z).

    pred right_distributive (o:'a -> 'b -> 'b) add =
      forall x y z, o x (add y z) = add (o x y) (o x z).

    pred left_loop inv (o:'a -> 'b -> 'b) =
      forall x, cancel (o x) (o (inv x)).

    pred rev_left_loop inv (o:'a -> 'b -> 'b) =
      forall x, cancel (o (inv x)) (o x).
  end SopTisT.
  export SopTisT.

  theory SopSisT.
    pred self_inverse e (o:'a -> 'a -> 'b) =
     forall x, o x x = e.

    pred commutative (o:'a -> 'a -> 'b) =
      forall x y, o x y = o y x.
  end SopSisT.
  export SopSisT.

  theory SopSisS.
    pred idempotent (o:'a -> 'a -> 'a) =
      forall x, o x x = x.

    pred associative (o:'a -> 'a -> 'a) =
      forall x y z, o x (o y z) = o (o x y) z.

    pred interchange op1 op2 =
      forall (x:'a) y z t, op1 (op2 x y) (op2 z t) = op2 (op1 x z) (op1 y t).
  end SopSisS.
  export SopSisS.
end OperationProperties.
export OperationProperties.

lemma nosmt inj_eq (f : 'a -> 'b):
  injective f => forall x y, (f x = f y) <=> (x = y).
proof. by move=> inj_f x y; split=> [| -> //]; apply inj_f. qed.

lemma nosmt can_eq (f : 'a -> 'b) g:
  cancel f g => forall x y, (f x = f y) <=> (x = y).
proof. by move=> can_fg; apply inj_eq; apply (can_inj f g). qed.

lemma nosmt can2_eq (f : 'a -> 'b) g:
  cancel f g => cancel g f => forall x y, (f x = y) <=> (x = g y).
proof. by move=> fK gK x y; rewrite -{1}gK; apply (can_eq f g). qed.
