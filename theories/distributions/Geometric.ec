require import AllCore Real RealSeq RealSeries Xreal StdOrder StdBigop List.
import RField RealOrder Xreal Distr DBool Bigreal.BRA.

section Parametrized.
(* The main parameter, generially the probability of success *)
declare op p : { real | 0%r < p <= 1%r } as in01_p.

(* Probability mass function. Note that this is the definition
   which starts at [n = 0]. *)
op g_mass i = if 0 <= i then p * (1%r - p) ^ i else 0%r.
op geometric = mk g_mass.

local lemma summable_mass : summable g_mass.
proof.
apply (summable_from_bounded _ (fun i => Some i)); 1: smt(). 
exists 1%r => n.
rewrite pmap_some map_id.
rewrite /partial (@eq_big_seq _ (fun i => p * (1%r - p) ^ i)).
- smt(mem_range in01_p expr_ge0).
case (0 <= n) => nat_n; 2: smt(big_geq).
rewrite -mulr_sumr.
apply ler_pdivl_mull; 1: smt(in01_p).
have -> : inv p * 1%r = (1%r / (1%r - (1%r - p))) by smt().
by apply Bigreal.sum_pow_le; smt(in01_p).
qed.

local lemma sum_mass : sum g_mass = 1%r. 
proof.
rewrite (sumEw _ (fun i => Some i) (fun i => 0 <= i) _ _ summable_mass); 1,2: smt(). 
have -> : (fun n => big predT g_mass (pmap (fun i => Some i) (range 0 n))) =
  (fun n => if 0 <= n then (1%r - (1%r - p) ^ n) else 0%r).
- apply/fun_ext => n. rewrite pmap_some map_id.
  rewrite (@eq_big_seq _ (fun i => p * (1%r - p) ^ i)).
  + smt(mem_range in01_p expr_ge0).
  case (0 <= n) => nat_n; 2: smt(big_geq).
  rewrite -mulr_sumr Bigreal.sum_pow; 1,2: smt(in01_p). 
  by field; smt(in01_p).
rewrite (lim_eq 0 _ (fun n => (1%r - (1%r - p) ^ n))); 1: by auto => />.
rewrite limD; 1: exact cnvC.
- by apply/cnvN/cnv_pow; smt(in01_p).
by rewrite limC limN lim_pow; 1: smt(in01_p).
qed.

lemma isdistr_geometric : isdistr g_mass.
proof.
apply isdistr_summable_equiv.
split; 1: smt(in01_p expr_ge0).
split; 1: exact summable_mass.
by apply/lerr_eq/sum_mass.
qed.

lemma geometric_ll : is_lossless geometric.
proof.
rewrite /is_lossless mu_mass.
have -> : (fun x => if predT x then mass geometric x else 0%r) = g_mass
  by smt(massK isdistr_geometric).
exact sum_mass.
qed.
end section Parametrized.

abstract theory ModuleBased.
op p : { real | 0%r < p < 1%r } as in01_p.

clone FixedBiased as Bernoulli
  with op p <- p
proof*.
realize in01_p by exact in01_p. 

op bernoulli = Bernoulli.dbiased.

module M = {
  (* Direct sampling *)
  proc sample() = {
      var i;
      i <$ geometric p;
      return i;
  }
  
  (* Rejection sampling from a bernoulli *)
  proc rej() = {
    var i <- -1;
    var b <- false;
    while (!b) {
      i <- i + 1;
      b <$ bernoulli;
    }
    return i;
  }
}.

section Proofs.
lemma rej_ll : islossless M.rej.
proof.
proc.
sp. conseq (: true ==> _) => //.
while (true) (b2i (!b)) 1 p; 1..3: smt().
- move=> H. seq 2 : true 1%r 1%r 0%r 0%r (true) => //.
  + auto; smt(Bernoulli.dbiased_ll).
- auto; smt(Bernoulli.dbiased_ll).
split; 1: smt(in01_p).
move => z. 
rnd. wp. skip.
rewrite Bernoulli.dbiasedE.
by auto => />. 
qed.

local lemma Ep_bool d f :
  Ep d f = mu1 d false ** f false + mu1 d true ** f true.
proof.
have -> := Ep_fin [false; true] d f _ _; 1,2: smt().
rewrite /big.
by have -> : map (d ** f) (filter predT [false; true]) =
  [(d ** f) false; (d ** f) true].
qed.

local lemma rej_bound &m k :
  Pr[ M.rej() @ &m : res = k ] <= g_mass p k.
proof.
byehoare => //.
proc.
while ((-1 <= i /\ (b => 0 <= i)) `|` (if b then b2r (i = k) else
  if i < k then p * (1%r - p) ^ (k - i - 1) else 0%r)%xr); 1,3: by auto => /#. 
wp. skip => /> &h. rewrite Ep_bool Bernoulli.dbiased1E Bernoulli.dbiased1E.
apply xle_cxr_r => /> *.
have -> /= : -1 <= i{h} + 1 by smt().
have -> /= : 0 <= i{h} + 1 by smt().
case (i{h} + 1 < k) => * />; first by smt(Domain.exprS).
smt(Domain.expr0).
qed.

lemma rej_distr &m k :
  Pr[ M.rej() @ &m : res = k ] = mu1 (geometric p) k.
proof.
rewrite Pr[mu1_le_eq_mu1 (geometric p)] => //.
- exact rej_ll.
move => ?. rewrite (muK _ _ (isdistr_geometric _ _)). 
- smt(in01_p).
exact rej_bound. 
qed.

equiv rej_equiv : M.rej ~ M.sample : true ==> ={res}.
bypr (res{1}) (res{2}) => // *.
rewrite rej_distr.
byphoare; 2,3: by auto.
proc. rnd. skip. by auto => />.
qed.
end section Proofs.
end ModuleBased.
