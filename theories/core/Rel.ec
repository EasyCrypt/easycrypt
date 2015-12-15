(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2015 - IMDEA Software Institute
 * Copyright (c) - 2012--2015 - Inria
 * 
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* Parts of this API have been imported from the [ssrbool] library of
 * the ssreflect library that is (c) Copyright Microsoft Corporation
 * and Inria. *)

require import ExtEq Pred Fun.

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
