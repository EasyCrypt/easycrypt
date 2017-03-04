(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2017 - Inria
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
require import Int Real NewDistr FSet Dfilter StdRing.
(*---*) import RField.

pragma +implicits.

(* -------------------------------------------------------------------- *)
op (\) (d : 'a distr) (P : 'a -> bool) : 'a distr = dscale (dfilter d P).

lemma support_dexcepted (x:'a) d P :
  support (d \ P) x <=> (support d x /\ !P x).
proof. by rewrite support_dscale support_dfilter /predI /predC. qed.

lemma mux_dexcepted d P (x : 'a) :
  mu_x (d \ P) x
  = if   P x
    then 0%r
    else (mu_x d x / (weight d - mu d (P))).
proof. by rewrite mux_dscale weight_dfilter mux_dfilter; case: (P x). qed.

lemma mu_dexcepted d P (E : 'a -> bool) :
  mu (d \ P) E
  = mu d (predI E (predC (P))) / (weight d - mu d (P)).
proof. by rewrite mu_dscale weight_dfilter mu_dfilter. qed.

lemma nosmt weight_dexcepted (d:'a distr) P :
  weight (d \ P) = b2r (weight d <> mu d (P)).
proof.
rewrite weight_dscale weight_dfilter /b2r subr_eq0.
by case: (weight d = mu d (P)).
qed.

lemma dexcepted_ll (d : 'a distr) P:
  is_lossless d => mu d (P) < 1%r =>
  is_lossless (d \ P).
proof.
move=> d_ll P_neq_d.
by rewrite /is_lossless -/(weight _) weight_dexcepted d_ll /#.
qed.
