(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2017 - Inria
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
require import Int Real List NewDistr RealExtra.
(*---*) import MUniform Range.

(* -------------------------------------------------------------------- *)
(* We keep intervals closed for now, to justify attaching the [_.._]
   notation to this distribution. *)
op dinter (i j : int) = duniform (range i (j + 1)).

(* -------------------------------------------------------------------- *)
lemma mux_dinter (i j : int) x:
  mu_x (dinter i j) x = if (i <= x <= j) then 1%r/(j - i + 1)%r else 0%r.
proof. by rewrite duniform1E mem_range undup_id 1:range_uniq size_range /#. qed.

(* -------------------------------------------------------------------- *)
lemma mu_dinter (i j : int) P:
  mu (dinter i j) P
  = (size (filter P (range i (j + 1))))%r / (max 0 (j - i + 1))%r.
proof. by rewrite duniformE undup_id 1:range_uniq size_range size_filter /#. qed.

(* -------------------------------------------------------------------- *)
lemma weight_dinter (i j : int):
  weight (dinter i j) = b2r (i <= j).
proof. by rewrite /weight mu_dinter filter_predT size_range /#. qed.

(* -------------------------------------------------------------------- *)
lemma support_dinter (i j : int) x:
  support (dinter i j) x <=> i <= x <= j.
proof. by rewrite /support /in_supp mux_dinter; case (i <= x <= j)=> //= /#. qed.

(* -------------------------------------------------------------------- *)
lemma dinter_suf (i j : int): is_subuniform (dinter i j).
proof.
move=> x y /support_dinter x_in_ij /support_dinter y_in_ij.
by rewrite !mux_dinter x_in_ij y_in_ij.
qed.

lemma dinter_uf (i j : int): i <= j => is_uniform (dinter i j).
proof.
move=> x_le_y; split; 2:exact/dinter_suf.
by rewrite /is_lossless -/(weight _) weight_dinter x_le_y b2r1.
qed.
