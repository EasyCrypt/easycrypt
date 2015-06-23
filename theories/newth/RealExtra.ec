(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2015 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-B licence.
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
require export Real.

pragma +implicits.

(* -------------------------------------------------------------------- *)
op lub (E : real -> bool) : real.

pred nonempty (E : real -> bool) =
  exists x, E x.

pred ub (E : real -> bool) (z : real) =
  forall y, E y => y <= z.

pred has_ub  (E : real -> bool) = nonempty (ub E).
pred has_lub (E : real -> bool) = nonempty E /\ has_ub E.

axiom lub_upper_bound (E : real -> bool): has_lub E => 
  forall x, E x => x <= lub E.

axiom lub_adherent (E : real -> bool): has_lub E =>
  forall eps, 0%r < eps =>
    exists e, E e /\ (lub E - eps) < e.
