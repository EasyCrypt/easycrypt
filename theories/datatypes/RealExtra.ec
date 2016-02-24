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
lemma divr0: forall x, x / 0%r = 0%r by done.

lemma invr0: inv 0%r = 0%r by done.

(* -------------------------------------------------------------------- *)
lemma b2rE (b : bool): b2r b = (b2i b)%r.
proof. by case: b. qed.

lemma le_b2r (b1 b2 : bool): (b1 => b2) <=> b2r b1 <= b2r b2.
proof. by rewrite /#. qed.

lemma b2r_ge0 (b : bool): 0%r <= b2r b.
proof. by case: b. qed.

lemma b2r0: b2r false = 0%r.
proof. by rewrite b2rE b2i0. qed.

lemma b2r1: b2r true = 1%r.
proof. by rewrite b2rE b2i1. qed.

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
by smt ml=0.

lemma nosmt lt_fromint (z1 z2 : int) :
  (z1%r < z2%r) <=> (z1 < z2)
by smt ml=0.

lemma nosmt fromint_abs  (z : int) : `|z|%r = `|z%r| by smt ml=0.

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

(* -------------------------------------------------------------------- *)
(* WARNING Lemmas used by tactics: *)
lemma nosmt upto2_abs (x1 x2 x3 x4 x5:real):
   0%r <= x1 =>
   0%r <= x3 =>
   x1 <= x5 =>
   x3 <= x5 =>
   x2 = x4 =>
   `|x1 + x2 - (x3 + x4)| <= x5 by [].

lemma nosmt upto2_notbad (ev1 ev2 bad1 bad2:bool) :
  ((bad1 <=> bad2) /\ (!bad2 => (ev1 <=> ev2))) =>
  ((ev1 /\ !bad1) <=> (ev2 /\ !bad2)) by [].

lemma nosmt upto2_imp_bad (ev1 ev2 bad1 bad2:bool) :
  ((bad1 <=> bad2) /\ (!bad2 => (ev1 <=> ev2))) =>
  (ev1 /\ bad1) => bad2 by [].

lemma nosmt upto_bad_false (ev bad2:bool) :
  !((ev /\ !bad2) /\ bad2) by [].

lemma nosmt upto_bad_or (ev1 ev2 bad2:bool) :
   (!bad2 => ev1 => ev2) => ev1 =>
    ev2 /\ !bad2 \/ bad2 by [].

lemma nosmt upto_bad_sub (ev bad:bool) :
  ev /\ ! bad => ev by [].
