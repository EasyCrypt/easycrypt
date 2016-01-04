(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2016 - Inria
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

require import Pred Real Distr.

op dfilter (d : 'a distr) (p : 'a -> bool): 'a distr.

axiom dfilterP (d : 'a distr) (p : 'a -> bool) (E : 'a -> bool):
  mu (dfilter d p) E = mu d (predI p E).

lemma dfilterE (d : 'a distr) (p : 'a -> bool) (x : 'a):
  mu_x (dfilter d p) x  = if (p x) then mu_x d x else 0%r.
proof.
  rewrite /mu_x dfilterP; case (p x)=> /= h.
    apply/mu_eq=> x'; rewrite /predI/pred1; case (x' = x)=> [->>|//=].
    by rewrite h.
  rewrite -(mu_false d); apply/mu_eq=> x'.
  rewrite /predI /pred1 /pred0 neqF; case (x' = x)=> [->|//=].
  by rewrite h.
qed.

lemma support_dfilter (d : 'a distr) (p : 'a -> bool) (x : 'a):
  support (dfilter d p) x <=> support d x /\ p x.
proof. by rewrite /support /in_supp dfilterE; case (p x). qed.

lemma weight_dfilter (d : 'a distr) (p : 'a -> bool):
  mu (dfilter d p) predT = mu d p.
proof. by rewrite dfilterP /predI /predT /= -etaE etaP. qed.
