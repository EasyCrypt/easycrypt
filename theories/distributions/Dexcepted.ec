(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
require import AllCore Distr FSet Dfilter StdRing.
(*---*) import RField.

pragma +implicits.

(* -------------------------------------------------------------------- *)
op (\) (d : 'a distr) (P : 'a -> bool) : 'a distr = dscale (dfilter d P).

lemma supp_dexcepted (x:'a) d P :
  support (d \ P) x <=> (support d x /\ !P x).
proof. by rewrite supp_dscale supp_dfilter /predI /predC. qed.

lemma dexcepted1E d P (x : 'a) :
  mu1 (d \ P) x
  = if   P x
    then 0%r
    else (mu1 d x / (weight d - mu d (P))).
proof. by rewrite dscale1E weight_dfilter dfilter1E; case: (P x). qed.

lemma nosmt dexcepted1E_notin (d : 'a distr) P x:
  !P x => mu1 (d \ P) x = (mu1 d x / (weight d - mu d (P))).
proof. by rewrite dexcepted1E => ->. qed.

lemma nosmt dexcepted1E_in d P (x:'a):
  P x => mu1 (d \ P) x = 0%r.
proof. by rewrite dexcepted1E => ->. qed.

lemma dexceptedE d P (E : 'a -> bool) :
  mu (d \ P) E
  = mu d (predI E (predC (P))) / (weight d - mu d (P)).
proof. by rewrite dscaleE weight_dfilter dfilterE. qed.

lemma nosmt weight_dexcepted (d:'a distr) P :
  weight (d \ P) = b2r (weight d <> mu d (P)).
proof.
rewrite weight_dscale weight_dfilter /b2r subr_eq0.
by case: (weight d = mu d (P)).
qed.

lemma dexcepted_ll (d : 'a distr) P:
  is_lossless d => mu d P < 1%r =>
  is_lossless (d \ P).
proof.
move=> d_ll P_neq_d.
by rewrite /is_lossless  weight_dexcepted d_ll /#.
qed.

lemma dexcepted_uni (d : 'a distr) P:
  is_uniform d => is_uniform (d \ P).
proof.
move=> uni x y; rewrite !supp_dexcepted !dexcepted1E. 
by move=> [? ->] [? ->] /=; congr; apply uni.
qed.


