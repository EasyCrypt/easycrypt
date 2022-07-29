require import AllCore Distr DBool Dfilter Dexcepted.
require import List Real RealSeries StdBigop.
import Bigreal BRA.

lemma dfilter_drestrict (d: 'a distr) (p: 'a -> bool) :
  dfilter d (predC p) = drestrict d p.
proof.
admitted.

op dcond (d : 'a distr) (p : 'a -> bool) = d \ predC p.

lemma dcond_ll (d: 'a distr) (p: 'a -> bool):
  mu d p > 0%r => is_lossless (dcond d p).
proof.
admitted.

lemma dcond_restrict (d: 'a distr) (p: 'a -> bool) :
  dcond d p = dscale (drestrict d p).
proof.
admitted.

lemma dcond_null (d: 'a distr) (p: 'a -> bool) :
  mu d p = 0%r => dcond d p = dnull.
proof.
admitted.

lemma dcond_supp (d: 'a distr) (p: 'a -> bool) (x: 'a):
  x \in dcond d p <=> x \in d /\ p x.
proof.
rewrite dcond_restrict supp_dscale supp_drestrict => //.
qed.

lemma weight_drestrict (d: 'a distr) (p: 'a -> bool) :
  weight (drestrict d p) = mu d p.
proof.
rewrite -dfilter_drestrict weight_dfilter.
suff: (weight d = mu d (predC p) + mu d p) by smt().
rewrite -mu_disjoint => /#.
qed.

lemma weight_dfilter_predC (d: 'a distr) (p: 'a -> bool) :
  weight (dfilter d (predC p)) = mu d p.
proof.
rewrite dfilter_drestrict weight_drestrict => //.
qed.

lemma dcond1E (d : 'a distr) (p : 'a -> bool) (x : 'a):
  mu1 (dcond d p) x = if p x then mu1 d x / mu d p else 0%r.
proof.
case (mu d p = 0%r).
  move => H.
  rewrite dcond_null => //=.
  case (p x); 2: smt(dnull1E).
  rewrite H; smt(dnull1E).
move => ?.
case (p x) => ?; 2: (suff: (x\notin dcond d p); smt(ge0_mu dcond_supp)).
rewrite /dcond /(\) /dscale => /=.
rewrite dscalar1E; 1: (rewrite weight_dfilter_predC; smt(ge0_mu)) => /=.
rewrite weight_dfilter_predC.
smt(dfilter_drestrict drestrict1E).
qed.

(* Chain rule of probability *)
lemma dcondE (d : 'a distr) (p : 'a -> bool) (p' : 'a -> bool) :
  mu (dcond d p) p' = mu d (predI p p') / mu d p.
proof.
rewrite dcond_restrict dscaleE.
congr.
- rewrite drestrictE => //.
- rewrite weight_drestrict => //.
qed.

lemma marginal_sampling (d : 'a distr) (f : 'a -> 'b) :
  d = dlet (dmap d f) (fun b => dcond d (fun a => f a = b)).
proof.
apply eq_distr => a.
rewrite dlet1E => /=.
rewrite (sumE_fin _ [f a]) => //=; 1: smt(dcond1E).
rewrite big_seq1 => /=.
rewrite dcond1E => /=.
case (a \in d); 2: smt(ge0_mu).
move => ?.
suff: mu1 (dmap d f) (f a) = mu d (fun a0 => f a0 = f a).
  have: (mu d (fun a0 => f a0 = f a) > 0%r) by smt(mu_sub).
  smt().
rewrite dmap1E /(\o) => /#.
qed.
