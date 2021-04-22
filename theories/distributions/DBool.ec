(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
require import AllCore List Distr Ring Number.
require import StdRing StdOrder StdBigop RealSeq RealSeries.
require (*--*) Bigop Bigalg.
(*---*) import RField RealOrder Bigreal.BRA.

(* -------------------------------------------------------------------- *)
clone include Distr.MFinite with
  type t            <- bool,
  op Support.enum <- [true; false],
  op Support.card <- 2
  rename "dunifinE" as "dboolE_count"
  rename "dunifin" as "dbool"
  rename "cunifin" as "cdbool"
proof Support.enum_spec by case.

lemma dboolE (E : bool -> bool):
  mu dbool E =   (if E true  then 1%r/2%r else 0%r)
               + (if E false then 1%r/2%r else 0%r).
proof. rewrite !dboolE_count /= /b2i /#. qed.

lemma dbool_leq b1 b2:
  (b1 => b2) =>
  mu1 dbool b1 <= mu1 dbool b2.
proof. by case b1; case b2=> //=; rewrite 2!dbool1E. qed.

(* -------------------------------------------------------------------- *)
theory Biased.
op clamp (p : real) = maxr 0%r (minr 1%r p).

lemma clamp_ge0 p : 0%r <= clamp p by move=> /#.
lemma clamp_le1 p : clamp p <= 1%r by move=> /#.

lemma clamp_id (p : real) : 0%r <= p <= 1%r => clamp p = p.
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

op dbiased (p : real) = Distr.mk (mbiased p).

lemma dbiased1E (p : real) (b : bool) :
  mu1 (dbiased p) b =
   if b then clamp p else 1%r - clamp p.
proof. by rewrite -massE muK  // isdistr_mbiased. qed.

lemma dbiasedE (p : real) (E : bool -> bool) :
  mu (dbiased p) E =
      (if E true  then       clamp p else 0%r)
    + (if E false then 1%r - clamp p else 0%r).
proof.
rewrite muE (@sumE_fin _ [true; false]) => [|[]|] //.
by rewrite 2!big_cons big_nil => @/predT /=; rewrite !massE !dbiased1E.
qed.

lemma supp_dbiased (p : real) b :
  0%r < p < 1%r => b \in (dbiased p).
proof.
case=> gt0_p lt1_p; rewrite /support /in_supp dbiased1E /#.
qed.

lemma dbiased_ll (p : real) : is_lossless (dbiased p).
proof. by rewrite /is_lossless dbiasedE /predT /= addrCA. qed.

lemma dbiased_fu (p : real) :
  0%r < p < 1%r => is_full (dbiased p).
proof.
by move=> ??;rewrite supp_dbiased.
qed.

end Biased.

(* -------------------------------------------------------------------- *)
abstract theory FixedBiased.

import Biased.

op p : {real | 0%r < p < 1%r} as in01_p.

op dbiased = Biased.dbiased p.

lemma dbiased1E (b : bool) :
  mu1 dbiased b = if b then p else 1%r - p.
proof. rewrite dbiased1E clamp_id //; smt (in01_p). qed.

lemma dbiasedE (E : bool -> bool) :
  mu dbiased E =
      (if E true  then       p else 0%r)
    + (if E false then 1%r - p else 0%r).
proof. rewrite dbiasedE !clamp_id //;smt(in01_p). qed.

lemma supp_dbiased x : x \in dbiased.
proof. by apply supp_dbiased;apply in01_p. qed.

lemma dbiased_ll : is_lossless dbiased.
proof. by apply dbiased_ll;apply in01_p. qed.

lemma dbiased_fu : is_full (dbiased p).
proof.
by move=> ?;rewrite /is_full supp_dbiased.
qed.

end FixedBiased.

(* -------------------------------------------------------------------- *)
import Biased Bigreal.

