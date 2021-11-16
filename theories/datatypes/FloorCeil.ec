(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2021 - Inria
 * Copyright (c) - 2012--2021 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
require import AllCore Ring StdRing StdOrder.
(*---*) import RField IntOrder RealOrder.

pragma +implicits.

lemma ceil_floor x : ceil x = - (floor (-x)).
proof.
rewrite eqr_le -le_fromint; split => [|_].
- have := floor_le (-x); rewrite ler_oppr -fromintN.
  rewrite -(@ler_add2r 1%r) => /(@ltr_le_trans _ _ _ (ceil_lt _)).
  by rewrite -fromintD !(le_fromint, lt_fromint) ltzS.
- have := floor_gt (-x); rewrite -ltr_opp2 opprB opprK => h.
  have := ceil_ge x; rewrite -(@ler_add2l 1%r).
  move/(ltr_le_trans _ _ _ h) => {h}; rewrite -fromintD.
  by rewrite -fromintN lt_fromint addzC ltzS.
qed.

lemma floor_mono (x y : real) : x <= y => floor x <= floor y.
proof.
move=> le_xy; rewrite -le_fromint; have := floor_gt y.
rewrite ltr_subl_addr => /(ler_lt_trans _ _ _ le_xy).
move/(ler_lt_trans _ _ _ (floor_le _)).
by rewrite -fromintD !(lt_fromint, le_fromint) ltzS.
qed.

lemma floorE (n : int, x : real) :
  n%r <= x < (n + 1)%r => floor x = n.
proof.
case=> gex lex; rewrite eqr_le; split=> [|_].
- by rewrite -ltzS -lt_fromint (ler_lt_trans _ _ lex) floor_le.
- by move/floor_mono: gex; rewrite from_int_floor.
qed.

lemma ceilE (n : int, x : real) :
  (n - 1)%r < x <= n%r => ceil x = n.
proof.
case=> gex lex; rewrite ceil_floor (@floorE (-n)) ?opprK //.
rewrite fromintN ler_opp2 lex /= -(@IntID.opprK ((-n) + 1)).
by rewrite fromintN ltr_opp2 addzC opprB.
qed.
