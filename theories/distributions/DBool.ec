(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2016 - Inria
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

require import Option Fun Pred Real List.
require (*--*) NewDistr.
(*
  (* FIXME: Countability witness for type bool... *)
  op elts = [true;false].

  op dbool (b : bool) = 1%r/2%r.

  lemma dbool_pos b: 0%r <= dbool b by [].

  lemma dbool_sum: SeriesSum.converge (fun i => dbool (nth witness elts i)) 1%r.
  proof. admit. qed.
*)

clone import NewDistr.MFinite as UniBool with
  type t            <- bool,
    op Support.enum <- [true; false],
    op Support.card <- 2
proof Support.enum_spec by case.

abbrev dbool = duniform.

lemma mu_dbool (p : bool -> bool):
  mu dbool p =   (if p true  then 1%r/2%r else 0%r)
               + (if p false then 1%r/2%r else 0%r).
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

lemma dbool_uf: Distr.is_subuniform dbool.
proof. by move=> x y; rewrite !dboolb. qed.

lemma dbool_fu: Distr.support dbool = predT.
proof. by apply/fun_ext; case; rewrite /support /in_supp /mu_x dboolb /#. qed.
