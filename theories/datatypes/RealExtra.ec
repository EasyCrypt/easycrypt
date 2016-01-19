(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2016 - Inria
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
require import Int IntExtra AlgTactic.
require export Real.

pragma +implicits.

(* -------------------------------------------------------------------- *)
lemma b2rE (b : bool): b2r b = (b2i b)%r.
proof. by case: b. qed.

lemma le_b2r (b1 b2 : bool): (b1 => b2) <=> b2r b1 <= b2r b2.
proof. by rewrite /#. qed.

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

(* -------------------------------------------------------------------- *)
lemma nosmt fromint0 : 0%r = Real.zero by [].
lemma nosmt fromint1 : 1%r = Real.one  by [].

lemma nosmt fromintN (z     : int) : (-z)%r = - z%r by [].
lemma nosmt fromintD (z1 z2 : int) : (z1 + z2)%r = z1%r + z2%r by [].
lemma nosmt fromintB (z1 z2 : int) : (z1 - z2)%r = z1%r - z2%r by [].
lemma nosmt fromintM (z1 z2 : int) : (z1 * z2)%r = z1%r * z2%r by [].

lemma nosmt eq_fromint (z1 z2 : int) :
  (z1%r = z2%r) <=> (z1 = z2)
by [].

lemma nosmt le_fromint (z1 z2 : int) :
  (z1%r <= z2%r) <=> (z1 <= z2)
by [].

lemma nosmt lt_fromint (z1 z2 : int) :
  (z1%r < z2%r) <=> (z1 < z2)
by [].

hint rewrite lte_fromint : le_fromint lt_fromint.

(* -------------------------------------------------------------------- *)
instance ring with real
  op rzero = Real.zero
  op rone  = Real.one
  op add   = Real.( + )
  op opp   = Real.([-])
  op mul   = Real.( * )
  op expr  = Real.( ^ )
  op ofint = Real.from_int

  proof oner_neq0 by smt ml=0
  proof addr0     by smt ml=0
  proof addrA     by smt ml=0
  proof addrC     by smt ml=0
  proof addrN     by smt ml=0
  proof mulr1     by smt ml=0
  proof mulrA     by smt ml=0
  proof mulrC     by smt ml=0
  proof mulrDl    by smt ml=0
  proof expr0     by smt w=(powr0 powrS powrN)
  proof exprS     by smt w=(powr0 powrS powrN)
  proof ofint0    by smt ml=0
  proof ofint1    by smt ml=0
  proof ofintS    by smt ml=0
  proof ofintN    by smt ml=0.

instance field with real
  op rzero = Real.zero
  op rone  = Real.one
  op add   = Real.( + )
  op opp   = Real.([-])
  op mul   = Real.( * )
  op expr  = Real.( ^ )
  op ofint = from_int
  op inv   = Real.inv

  proof oner_neq0 by smt ml=0
  proof addr0     by smt ml=0
  proof addrA     by smt ml=0
  proof addrC     by smt ml=0
  proof addrN     by smt ml=0
  proof mulr1     by smt ml=0
  proof mulrA     by smt ml=0
  proof mulrC     by smt ml=0
  proof mulrDl    by smt ml=0
  proof mulrV     by smt ml=0
  proof expr0     by smt w=(powr0 powrS powrN)
  proof exprS     by smt w=(powr0 powrS powrN)
  proof exprN     by smt w=(powr0 powrS powrN)
  proof ofint0    by smt ml=0
  proof ofint1    by smt ml=0
  proof ofintS    by smt ml=0
  proof ofintN    by smt ml=0.
