(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2016 - Inria
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

require import Option Fun Pred Real RealExtra List NewDistr.
require import Ring Number StdRing StdOrder StdBigop RealSeq RealSeries.
require (*--*) Bigop Bigalg.
(*---*) import RField RealOrder Bigreal.BRA.

clone import NewDistr.MFinite as UniBool with
  type t            <- bool,
    op Support.enum <- [true; false],
    op Support.card <- 2
proof Support.enum_spec by case.

abbrev dbool = dunifin.

lemma mu_dbool (E : bool -> bool):
  mu dbool E =   (if E true  then 1%r/2%r else 0%r)
               + (if E false then 1%r/2%r else 0%r).
proof. by rewrite !duniformE /= /#. qed.

lemma dbool_pred0: mu dbool pred0 = 0%r.
proof. by rewrite mu_dbool. qed.

lemma dbool_predT: mu dbool predT = 1%r.
proof. by rewrite mu_dbool. qed.

lemma dboolb b: mu dbool (pred1 b) = 1%r/2%r.
proof. by case b; rewrite mu_dbool. qed.

lemma dbool_leq b1 b2:
  (b1 => b2) =>
  mu dbool (pred1 b1) <= mu dbool (pred1 b2).
proof. by case b1; case b2=> //=; rewrite 2!dboolb. qed.

lemma dbool_ll : is_lossless dbool.
proof. by apply/UniBool.dunifin_ll. qed.

lemma dbool_uf: is_subuniform dbool.
proof. by move=> x y; rewrite !dboolb. qed.

lemma dbool_fu: Distr.support dbool = predT.
proof. by apply/UniBool.duniform_fu. qed.

(* -------------------------------------------------------------------- *)
theory Biased.
op clamp (p : real) = maxr 0%r (minr 1%r p).

lemma clamp_ge0 p : 0%r <= clamp p by move=> /#.
lemma clamp_le1 p : clamp p <= 1%r by move=> /#.

lemma clamp_id (p : real) : 0%r < p < 1%r => clamp p = p.
proof. by move=> /#. qed.

op mbiased (p : real) =
  fun b => if b then clamp p else 1%r - clamp p.

lemma ge0_mbiased (p : real) :
  forall b, 0%r <= mbiased p b.
proof. by move=> /#. qed.

lemma isdistr_mbiased p : isdistr (mbiased p).
proof.
apply/(isdistr_finP [true; false])=> //.
  by case. by apply/ge0_mbiased.
by rewrite 2!big_cons big_nil => @/predT /= /#.
qed.

op dbiased (p : real) = NewDistr.mk (mbiased p).

lemma dbiasedE (p : real) (b : bool) :
  mu_x (dbiased p) b =
   if b then clamp p else 1%r - clamp p.
proof. by rewrite muK  // isdistr_mbiased. qed.

lemma prbiasedE (p : real) (E : bool -> bool) :
  mu (dbiased p) E =
      (if E true  then       clamp p else 0%r)
    + (if E false then 1%r - clamp p else 0%r).
proof.
rewrite muE (@sumE_fin _ [true; false]) => [|[]|] //.
by rewrite 2!big_cons big_nil => @/predT /=; rewrite !dbiasedE.
qed.

lemma dbiased_ll (p : real) : is_lossless (dbiased p).
proof. by rewrite /is_lossless prbiasedE /predT /= addrCA. qed.

lemma dbiased_fu (p : real):
  0%r < p < 1%r => support (dbiased p) = predT.
proof.
case=> gt0_p lt1_p; apply/fun_ext=> b.
by rewrite /support /in_supp dbiasedE /#.
qed.
end Biased.

(* -------------------------------------------------------------------- *)
abstract theory FixedBiased.

import Biased.

op p : {real | 0%r < p < 1%r} as in01_p.

op dbiased = Biased.dbiased p.

lemma dbiasedE (b : bool) :
  mu_x dbiased b = if b then p else 1%r - p.
proof. by rewrite dbiasedE clamp_id ?in01_p. qed.

lemma prbiasedE (E : bool -> bool) :
  mu dbiased E =
      (if E true  then       p else 0%r)
    + (if E false then 1%r - p else 0%r).
proof. by rewrite prbiasedE !clamp_id ?in01_p. qed.

lemma dbiased_ll : is_lossless dbiased.
proof. by apply/dbiased_ll. qed.

lemma dbiased_fu : support dbiased = predT.
proof. by apply/dbiased_fu/in01_p. qed.
end FixedBiased.
