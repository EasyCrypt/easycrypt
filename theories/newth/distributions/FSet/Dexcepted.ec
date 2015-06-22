(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2015 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-B licence.
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
require import Int Real Distr NewFSet Drestrict.

pragma +implicits.

(* -------------------------------------------------------------------- *)
op (\) (d:'a distr, X:'a fset) : 'a distr = Dscale.dscale (drestr d X).

lemma supp_def (x:'a) d X:
  in_supp x (d \ X) <=> (in_supp x d /\ !mem X x).
proof. by rewrite /(\) Dscale.supp_def supp_def. qed.

lemma mu_x_def (x:'a) d X:
  mu_x (d \ X) x =
  (in_supp x (d \ X)) ? mu_x d x / (weight d - mu d (mem X)) : 0%r.
proof.
  rewrite /(\); case (weight d - mu d (mem X) = 0%r)=> weight.
    by rewrite /mu_x Dscale.mu_def_0 ?weight_def //
               /in_supp
               (_: (0%r < mu_x (Dscale.dscale (drestr d X)) x) = false)=> //=;
       first smt.
    by smt.
qed.

lemma nosmt mu_weight_def (d:'a distr) X:
  weight (d \ X) = (weight d = mu d (mem X)) ? 0%r : 1%r.
proof.
  case (weight d = mu d (mem X))=> weight_d //=.
    by rewrite /weight /(\) Dscale.mu_def_0 // weight_def weight_d; smt.
    by rewrite /(\) Dscale.weight_pos // weight_def; smt.
qed.

lemma lossless_restr (d:'a distr) X:
  weight d = 1%r =>
  mu d (mem X) < 1%r =>
  Distr.weight (d \ X) = 1%r. 
proof.
 intros Hll Hmu; simplify (\);
 (rewrite Distr.Dscale.weight_pos;last smt);
 rewrite weight_def;smt.
qed.
