(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2017 - Inria
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* Parts of this API have been imported from the [ssrbool] library of
 * the ssreflect library that is (c) Copyright Microsoft Corporation
 * and Inria. *)

require import ExtEq Pred Fun.

type 'a rel = 'a -> 'a -> bool.

(* -------------------------------------------------------------------- *)
pred total ['a] (R : 'a -> 'a -> bool) = forall x y, R x y \/ R y x.

pred transitive ['a] (R : 'a -> 'a -> bool) =
  forall y x z, R x y => R y z => R x z.

(* -------------------------------------------------------------------- *)
pred symmetric ['a] (R : 'a -> 'a -> bool) = forall x y, R x y = R y x.

pred antisymmetric ['a] (R : 'a -> 'a -> bool) =
  forall x y, R x y /\ R y x => x = y.

pred pre_symmetric ['a] (R : 'a -> 'a -> bool) =
  forall x y, R x y => R y x.

(* -------------------------------------------------------------------- *)
lemma symmetric_from_pre ['a] (R : 'a -> 'a -> bool) :
  pre_symmetric R => symmetric R.
proof. by move=> symR x y; rewrite eq_iff; split; apply: symR. qed.

(* -------------------------------------------------------------------- *)
pred reflexive ['a] (R : 'a -> 'a -> bool) = forall x, R x x.

pred irreflexive ['a] (R : 'a -> 'a -> bool) = forall x, !R x x.

(* -------------------------------------------------------------------- *)
pred left_transitive ['a] (R : 'a -> 'a -> bool) =
  forall x y, R x y => R x == R y.

pred right_transitive ['a] (R : 'a -> 'a -> bool) =
  forall x y, R x y => transpose R x == transpose R y.

(* -------------------------------------------------------------------- *)
lemma sym_left_transitive ['a] (R : 'a -> 'a -> bool) :
  symmetric R =>
  transitive R =>
  left_transitive R.
proof.
move=> symR trR x y Rxy z; rewrite eq_iff.
by split; apply: trR; rewrite // symR.
qed.

lemma sym_right_transitive ['a] (R : 'a -> 'a -> bool) :
  symmetric R =>
  transitive R =>
  right_transitive R.
proof.
move=> symR trR x y /(sym_left_transitive _ symR trR) Rxy z.
by rewrite !(symR z) Rxy.
qed.

(* -------------------------------------------------------------------- *)
pred equivalence_rel ['a] (R : 'a -> 'a -> bool) =
  forall x y z, R z z /\ (R x y => R x z = R y z).

(* -------------------------------------------------------------------- *)
lemma equivalence_relP ['a] (R : 'a -> 'a ->  bool) :
  equivalence_rel R <=> reflexive R /\ left_transitive R.
proof.
split=> [eqiR|[Rxx trR] x y z]; last by split; [apply:Rxx|move=>/trR->].
by split=> [x|x y Rxy z]; rewrite ?(eqiR x x x) ?(andEr _ _ (eqiR x y z)).
qed.

(* -------------------------------------------------------------------- *)
lemma rev_trans ['a] (R : 'a -> 'a -> bool) :
  transitive R => transitive (transpose R).
proof. by move=> trR x y z Ryx Rzy; apply: (trR _ _ _ Rzy Ryx). qed.

(* -------------------------------------------------------------------- *)
lemma rel_ext (P Q : 'a -> 'b -> bool):
  P = Q <=> forall a b, P a b <=> Q a b.
proof. by split=> //= h; apply/fun_ext=> a; apply/fun_ext=> b; rewrite h. qed.

(*** Working with relations ***)
(** Lifting boolean operators to relations *)
op rel0  ['a 'b] = fun (x : 'a) (y : 'b) => false.
op relT  ['a 'b] = fun (x : 'a) (y : 'b) => true.
op relI  ['a 'b] = fun (p1 p2 : 'a -> 'b -> bool) a b => p1 a b /\ p2 a b.
op relU  ['a 'b] = fun (p1 p2 : 'a -> 'b -> bool) a b => p1 a b \/ p2 a b.
op relC  ['a 'b] = fun (p : 'a -> 'b -> bool) a b => ! (p a b).
op relD  ['a 'b] = fun (p1 p2 : 'a -> 'b -> bool) a b => !p2 a b /\ p1 a b.

op rel1  ['a 'b] = fun (ca : 'a) (cb : 'b) a b => ca = a /\ cb = b.
op relU1 ['a 'b] = fun (ca : 'a) (cb : 'b) (p : 'a -> 'b -> bool) (a : 'a) (b : 'b)=>
                     (a = ca /\ b = cb) \/ p a b.
op relC1 ['a 'b] = fun (ca : 'a) (cb : 'b) (a : 'a) (b : 'b) => a <> ca /\ b <> cb.
op relD1 ['a 'b] = fun (p : 'a -> 'b -> bool) (ca : 'a) (cb : 'b) (a : 'a) (b : 'b)=>
                     (a <> ca \/ b <> cb) /\ p a b.

(** Subrelation *)
pred subrel (r1 r2 : 'a -> 'b -> bool) = forall x y, r1 x y => r2 x y.

(* Lemmas on relation inclusion *)
lemma nosmt subrel_eqP (r1 r2 : 'a -> 'b -> bool):
  (forall x y, r1 x y <=> r2 x y) <=> (subrel r1 r2 /\ subrel r2 r1)
by [].

lemma nosmt subrel_refl (r : 'a -> 'b -> bool): subrel r r
by [].

lemma nosmt subrel_asym (r1 r2 : 'a -> 'b -> bool):
  subrel r1 r2 => subrel r2 r1 => r1 = r2.
proof.
  move=> subrel_r1_r2 subrel_r2_r1.
  (* Binary Extensional Equality *)
  apply/fun_ext=> x.
  apply/fun_ext=> y.
  smt.
qed.

lemma nosmt subrel_trans (r2 r1 r3 : 'a -> 'b -> bool):
  subrel r1 r2 => subrel r2 r3 => subrel r1 r3
by [].

(** Lemmas **)
lemma relIC (p1 p2 : 'a -> 'b -> bool) : relI p1 p2 = relI p2 p1.
proof. by apply/rel_ext=> a b; rewrite /relI andC. qed.

lemma relCrelI (p : 'a -> 'b -> bool) : relI (relC p) p = rel0.
proof. by apply/rel_ext=> a b /=; case: (p a b); delta=> ->. qed. (* delta *)

lemma relCrelU (p : 'a -> 'b -> bool) : relU (relC p) p = relT.
proof. by apply/rel_ext=> a b /=; case: (p a b); delta=> ->. qed. (* delta *)

lemma nosmt subrelUl (p1 p2 : 'a -> 'b -> bool):
  subrel p1 (relU p1 p2)
by [].

lemma nosmt subrelUr (p1 p2 : 'a -> 'b -> bool):
  subrel p2 (relU p1 p2)
by [].

lemma nosmt relIsubrell (p1 p2 : 'a -> 'b -> bool):
  subrel (relI p1 p2) p1
by [].

lemma nosmt relIsubrelr (p1 p2 : 'a -> 'b -> bool):
  subrel (relI p1 p2) p2
by [].
