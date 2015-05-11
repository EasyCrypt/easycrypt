(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2015 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-B licence.
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
require import Bool Option Fun Distr Int IntExtra Real NewRealOrder NewList.
(*---*) import IterOp.
require (*--*) NewBigop.

pragma +implicits.

(* -------------------------------------------------------------------- *)
clone import NewBigop as Series with
  type t <- real,
  op Support.idm <- 0%r,
  op Support.(+) <- Real.(+).

(* -------------------------------------------------------------------- *)
theory SeriesConvergence.
  pred converge (s : int -> real) (x : real) =
    forall epsilon, 0%r <= epsilon => exists alpha,
      forall n, (alpha <= n)%Int => `|s n - x| < epsilon.

  lemma converge_uniq (s : int -> real) (x1 x2 : real):
    converge s x1 => converge s x2 => x1 = x2.
  proof. admit. qed.
end SeriesConvergence.

(* -------------------------------------------------------------------- *)
theory SeriesSum.
  op partial (s : int -> real) (n : int) : real =
    sum predT s (iota_ 0 n).

  pred converge (s : int -> real) (x : real) =
    SeriesConvergence.converge (partial s) x.
end SeriesSum.
