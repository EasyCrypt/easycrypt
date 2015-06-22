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
clone import NewBigop as RSum with
  type t <- real,
  op Support.idm <- 0%r,
  op Support.(+) <- Real.(+).

(* -------------------------------------------------------------------- *)
(* FIXME: factor out this and implement match expressions!              *)
op pmap ['a 'b] (f : 'a -> 'b option) (s : 'a list) =
  with s = "[]"     => []
  with s = (::) x s =>
    if f x = None then pmap f s else oget (f x) :: pmap f s.

(* -------------------------------------------------------------------- *)
theory SeriesConvergence.
  pred converge (s : int -> real) (x : real) =
    forall epsilon, 0%r <= epsilon => exists alpha,
      forall n, (alpha <= n)%Int => `|s n - x| < epsilon.
end SeriesConvergence.

op lim (s : int -> real) : real.

(* -------------------------------------------------------------------- *)
theory SeriesSum.
  op partial (s : int -> real) (n : int) : real =
    bigi predT s 0 n.

  pred converge (s : int -> real) (x : real) =
    SeriesConvergence.converge (partial s) x.
end SeriesSum.

(* -------------------------------------------------------------------- *)
pred countable ['a] (E : 'a -> bool) =
  exists (C : int -> 'a option),
    forall x, E x => exists i, C i = Some x.

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

(* -------------------------------------------------------------------- *)
theory NewDistr.
  type 'a distr.

  op mu : 'a distr -> ('a -> real).

  axiom ge0_mu ['a] (d : 'a distr) (x : 'a):
    0%r <= mu d x.

  axiom le1_mu ['a] (d : 'a distr) (x : 'a):
    forall (s : 'a list), uniq s =>
      RSum.big predT (mu d) s <= 1%r.

  axiom countable_mu ['a] (d : 'a distr):
    countable (fun x => mu d x <> 0%r).

  op prS ['a] (E : 'a -> bool) (d : 'a distr) :
    { real -> bool | forall x, prS x <=>
        exists (s : 'a list), uniq s /\ x = RSum.big E (mu d) s }
    as prSP.

  op pr ['a] (E : 'a -> bool) (d : 'a distr) = lub (prS E d).

  lemma prE ['a] (E : 'a -> bool) (d : 'a distr):
    forall (s : int -> 'a option),
         (forall i j x, s i = Some x => s j = Some x => i = j)
      => (forall x, mu d x <> 0%r => exists i, 0 <= i /\ s i = Some x)
      => pr E d = lim (fun n => big E (mu d) (pmap s (range 0 n))).
  proof. admit. qed.
end NewDistr.
