(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2016 - Inria
 * 
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
require import Int IntExtra.
require export Real.

pragma +implicits.

(* -------------------------------------------------------------------- *)
lemma b2rE (b : bool): b2r b = (b2i b)%r.
proof. by case: b. qed.

lemma le_b2r (b1 b2 : bool): (b1 => b2) <=> b2r b1 <= b2r b2.
proof. by rewrite !b2rE FromInt.from_intMle -le_b2i. qed.

lemma b2r_ge0 (b : bool): 0%r <= b2r b.
proof. by case: b. qed.

(* -------------------------------------------------------------------- *)
op lub (E : real -> bool) : real.

op nonempty (E : real -> bool) =
  exists x, E x.

op ub (E : real -> bool) (z : real) =
  forall y, E y => y <= z.

op has_ub  (E : real -> bool) = nonempty (ub E).
op has_lub (E : real -> bool) = nonempty E /\ has_ub E.

axiom lub_upper_bound (E : real -> bool): has_lub E => 
  forall x, E x => x <= lub E.

axiom lub_adherent (E : real -> bool): has_lub E =>
  forall eps, 0%r < eps =>
    exists e, E e /\ (lub E - eps) < e.
