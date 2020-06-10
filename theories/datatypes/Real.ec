(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
require import Int Ring AlgTactic CoreReal.

abbrev ( < ) = CoreReal.lt.
abbrev (<= ) = CoreReal.le.
abbrev ( + ) = CoreReal.add.
abbrev ([-]) = CoreReal.opp.
abbrev ( * ) = CoreReal.mul.
abbrev inv   = CoreReal.inv.

abbrev ( - ) (x y : real) = x + (-y).
abbrev ( / ) (x y : real) = x * (inv y).

abbrev [-printing] ( >  ) (x y : real) = y < x.
abbrev [-printing] ( >= ) (x y : real) = y <= x.

(* -------------------------------------------------------------------- *)
op "`|_|" x = if from_int 0 <= x then x else -x.
abbrev b2r (b:bool) = if b then from_int 1 else from_int 0.

(* -------------------------------------------------------------------- *)

lemma nosmt fromint0 : 0%r = CoreReal.zero by [].
lemma nosmt fromint1 : 1%r = CoreReal.one  by [].

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

theory RField.
  clone include Ring.Field with
    type t <- real,
    op   zeror <- 0%r,
    op   oner  <- 1%r,
    op   ( + ) <- CoreReal.add,
    op   [ - ] <- CoreReal.opp,
    op   ( * ) <- CoreReal.mul,
    op   invr  <- CoreReal.inv
    proof *
  remove abbrev (-) remove abbrev (/).
  realize addrA     by smt().
  realize addrC     by smt().
  realize add0r     by smt().
  realize addNr     by smt().
  realize oner_neq0 by smt().
  realize mulrA     by smt().
  realize mulrC     by smt().
  realize mul1r     by smt().
  realize mulrDl    by smt().
  realize mulVr     by rewrite /left_inverse_in /#.
  realize unitP     by smt().
  realize unitout   by move=> x /= ->. 
  realize mulf_eq0  by smt().

  lemma nosmt ofintR (i : int): ofint i = i%r.
  proof.
  have h: forall i, 0 <= i => ofint i = i%r.
  + elim=> [|j j_ge0 ih] //=; first by rewrite ofint0.
    by rewrite ofintS // fromintD ih addrC.
  elim/natind: i=> [n|/#].
  by rewrite -oppz_ge0 -eqr_opp -ofintN -fromintN; exact/h.
  qed.

  lemma intmulr x c : intmul x c = x * c%r.
  proof.
    have h: forall cp, 0 <= cp => intmul x cp = x * cp%r.
      elim=> /= [|cp ge0_cp ih].
        by rewrite mulr0z.
      by rewrite mulrS // ih fromintD mulrDr mulr1 addrC.
    case: (lezWP c 0) => [le0c|_ /h //].
    rewrite -{2}(@oppzK c) fromintN mulrN -h 1:smt.
    by rewrite mulrNz opprK.
  qed.

  lemma nosmt double_half (x : real) : x / 2%r + x / 2%r = x.
  proof. by rewrite -ofintR -mulrDl -mul1r2z -mulrA divff // ofintR. qed.

end RField.
import RField.

abbrev ( ^ ) = RField.exp.

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
op intp x = choiceb (fun i => i%r <= x < (i+1)%r) 0.

axiom le_intp x : (intp x)%r <= x.
axiom gt_intp x : x < (intp x + 1)%r.

lemma leup_intp z x : z%r <= x => z <= intp x.
proof.
by move=> le_zx; have := le_intp x; have := gt_intp x => /#.
qed.

(* -------------------------------------------------------------------- *)
instance ring with real
  op rzero = CoreReal.zero
  op rone  = CoreReal.one
  op add   = CoreReal.add
  op opp   = CoreReal.opp
  op mul   = CoreReal.mul
  op expr  = RField.exp
  op ofint = CoreReal.from_int

  proof oner_neq0 by smt ml=0
  proof addr0     by smt ml=0
  proof addrA     by smt ml=0
  proof addrC     by smt ml=0
  proof addrN     by smt ml=0
  proof mulr1     by smt ml=0
  proof mulrA     by smt ml=0
  proof mulrC     by smt ml=0
  proof mulrDl    by smt ml=0
  proof expr0     by smt w=(expr0 exprS exprN)
  proof exprS     by smt w=(expr0 exprS exprN)
  proof ofint0    by smt ml=0
  proof ofint1    by smt ml=0
  proof ofintS    by smt ml=0
  proof ofintN    by smt ml=0.

instance field with real
  op rzero = CoreReal.zero
  op rone  = CoreReal.one
  op add   = CoreReal.add
  op opp   = CoreReal.opp
  op mul   = CoreReal.mul
  op expr  = RField.exp
  op ofint = CoreReal.from_int
  op inv   = CoreReal.inv

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
  proof expr0     by smt w=(expr0 exprS exprN)
  proof exprS     by smt w=(expr0 exprS exprN)
  proof exprN     by smt w=(expr0 exprS exprN)
  proof ofint0    by smt ml=0
  proof ofint1    by smt ml=0
  proof ofintS    by smt ml=0
  proof ofintN    by smt ml=0.

(* -------------------------------------------------------------------- *)
op floor : real -> int.
op ceil  : real -> int.

axiom floor_bound (x:real) : x - 1%r <= (floor x)%r <= x.
axiom  ceil_bound (x:real) : x <= (ceil x)%r <= x + 1%r.
axiom from_int_floor n : floor n%r = n.
axiom from_int_ceil  n : ceil  n%r = n.

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

