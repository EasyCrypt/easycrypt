(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
require import AllCore List Distr.
(*---*) import MUniform Range.

(* -------------------------------------------------------------------- *)
(* We keep intervals closed for now, to justify attaching the [_.._]
   notation to this distribution. *)
op dinter (i j : int) = duniform (range i (j + 1)).

lemma dinter1E (i j : int) x:
  mu1 (dinter i j) x = if (i <= x <= j) then 1%r/(j - i + 1)%r else 0%r.
proof. by rewrite duniform1E mem_range undup_id 1:range_uniq size_range /#. qed.

lemma dinterE (i j : int) P:
  mu (dinter i j) P
  = (size (filter P (range i (j + 1))))%r / (max 0 (j - i + 1))%r.
proof. by rewrite duniformE undup_id 1:range_uniq size_range size_filter /#. qed.

lemma weight_dinter (i j : int):
  weight (dinter i j) = b2r (i <= j).
proof. by rewrite /weight dinterE filter_predT size_range /#. qed.

lemma supp_dinter (i j : int) x:
  x \in (dinter i j) <=> i <= x <= j.
proof. by rewrite /support /in_supp dinter1E; case (i <= x <= j)=> //= /#. qed.

lemma dinter_ll (i j : int): i <= j => is_lossless (dinter i j).
proof. move=> Hij;apply /drange_ll => /#. qed.

lemma dinter_uni (i j : int): is_uniform (dinter i j).
proof. apply drange_uni. qed.

