(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2016 - Inria
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
require import Int Real NewDistr FSet Drestrict StdRing.
(*---*) import RField.

pragma +implicits.

(* -------------------------------------------------------------------- *)
op (\) (d : 'a distr) (X : 'a fset) : 'a distr = dscale (drestr d X).

lemma support_dexcepted (x:'a) d X :
  support (d \ X) x <=> (support d x /\ !mem X x).
proof. by rewrite support_dscale support_drestr /predI /predC. qed.

lemma mux_dexcepted d X (x : 'a) :
  mu_x (d \ X) x
  = if   mem X x
    then 0%r
    else (mu_x d x / (weight d - mu d (mem X))).
proof. by rewrite mux_dscale weight_drestr mux_drestr; case: (mem X x). qed.

lemma mu_dexcepted d X (E : 'a -> bool) :
  mu (d \ X) E
  = mu d (predI E (predC (mem X))) / (weight d - mu d (mem X)).
proof. by rewrite mu_dscale weight_drestr mu_drestr. qed.

lemma nosmt weight_dexcepted (d:'a distr) X :
  weight (d \ X) = b2r (weight d <> mu d (mem X)).
proof.
rewrite weight_dscale weight_drestr /b2r subr_eq0.
by case: (weight d = mu d (mem X)).
qed.

lemma dexcepted_ll (d : 'a distr) X:
  is_lossless d =>
  mu d (mem X) < 1%r =>
  is_lossless (d \ X).
proof.
move=> d_ll X_neq_d.
by rewrite /is_lossless -/(weight _) weight_dexcepted d_ll /#.
qed.
