(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2016 - Inria
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
require import Int Real Distr FSet Drestrict.

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
    rewrite Dscale.supp_def Dscale.mu_def_pos ?weight_def 1:smt Drestrict.supp_def.
    case: (in_supp x d)=> /= [x_in_d|x_notin_d]; first last.
    + have: !in_supp x (drestr d X) by rewrite Drestrict.supp_def x_notin_d.
      smt.
    case (!mem X x)=> /= [x_notin_X|x_in_X].
    + by rewrite mu_x_def_notin.
    by rewrite mu_x_def_in.
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
 move=> Hll Hmu; simplify (\);
 (rewrite Distr.Dscale.weight_pos;last smt);
 rewrite weight_def;smt.
qed.
