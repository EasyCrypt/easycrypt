require import AllCore List FSet Distr DProd DList StdBigop StdOrder.
(*---*) import Bigreal RealSeries RealOrder RField.

(********** preliminaries (to move) ***************************************)

(* lub for functions *)
op flub (F : 'a -> real) : real = lub (fun r => exists a, F a = r).

lemma flub_sup r (F : 'a -> real) x : 
    (forall x, F x <= r) => F x <= flub F.
proof.
move => H. apply lub_upper_bound; 2: by exists x.
split; [by exists (F x) x|exists r => y [a] <-; exact H].
qed.

lemma ler_flub (F : 'a -> real) r :
    (forall x, F x <= r) => flub F <= r.
proof.
move => H. 
have ub_r : ub (fun (x : real) => exists (a : 'a), F a = x) r. 
  move => y [a] <-; exact H.
apply RealLub.lub_le_ub => //. 
split; [by exists (F witness) witness| by exists r].
qed.

(* DList.ec *)
lemma weight_dlist (d : 'a distr) n : 0 <= n => weight (dlist d n) = (weight d)^n.
proof.
elim: n => [|n ? IHn]; 1: by rewrite weight_dlist0 // expr0.
by rewrite weight_dlistS // IHn exprS.
qed.

(* additional lemmas for summable *)

(* subsumes summable_bij *)
lemma summable_inj (h : 'a -> 'b) (s : 'b -> real) : 
  injective h => summable s => summable (s \o h).
proof.
move => inj_h [M] sum_s; exists M => J uniq_J. 
have R := sum_s (map h J) _; 1: by rewrite map_inj_in_uniq /#.
apply (ler_trans _ _ _ _ R) => {R}. 
rewrite BRA.big_map /(\o)/= BRA.big_mkcond.
have -> : (fun (x : 'a) => predT (h x)) = predT by apply/fun_ext.
apply Bigreal.ler_sum; smt().
qed.

lemma summable_cond p (s : 'a -> real) : 
  summable s => summable (fun x => if p x then s x else 0%r).
proof. 
case => r Hr; exists r => J uniJ; apply (ler_trans _ _ _ _ (Hr J uniJ)).
by apply ler_sum_seq => /=; smt().
qed.

lemma summableN (s : 'a -> real) : summable s => summable (fun x => - s x).
proof.
by move => sum_s; apply (summable_le _ _ sum_s) => /= a; rewrite normrN.
qed.

lemma norm_summable (s : 'a -> real) : summable (fun x => `|s x|) => summable s.
proof. 
move => sum_s; apply (summable_le _ _ sum_s) => /= a. 
by rewrite (ger0_norm `|s a|) ?normr_ge0.
qed.

lemma summable_mu1 (d : 'a distr) : summable (fun x => mu1 d x).
proof. 
rewrite (eq_summable _ (mass d)) /= => [x|]; 1: by rewrite massE.
exact summable_mass.
qed.

lemma summable_mu1_cond p (d : 'a distr) : 
  summable (fun x => if p x then mu1 d x else 0%r).
proof. exact/summable_cond/summable_mu1. qed.

lemma summable_sdist (d1 d2 : 'a distr) : 
  summable (fun x => `| mu1 d1 x - mu1 d2 x |).
proof. 
apply/summable_norm/summableD; 1: exact/summable_mu1. 
exact/summableN/summable_mu1.
qed.

(* should replace summable_pswap, whoch proves only one direction *)
lemma summable_pswap (s : 'a * 'b -> real) : summable s <=> summable (s \o pswap).
proof.
split => [|H]; 1: exact summable_pswap.
have -> : s = (s \o pswap) \o pswap by apply/fun_ext => -[].
exact summable_pswap.
qed.

(* name clash *)
lemma summableM' (s1 s2 : 'a -> real) : 
  summable s1 => summable s2 => summable (fun x => s1 x * s2 x).
proof.
move => sum_s1 sum_s2. 
have H := summableM _ _ sum_s1 sum_s2.
have := summable_inj (fun x : 'a => (x,x)) _ _ H. smt().
move => sum_s. exact(summable_le _ _ sum_s).
qed.

lemma ler_sum_norm (s : 'a -> real) : 
  summable s => sum s <= sum (fun x => `|s x|).
proof.
move => sum_s; apply ler_sum => // => [x|]; 1: exact ler_norm. 
exact summable_norm.
qed.

lemma norm_sum_sum (s : 'a -> real) : 
  summable s => `| sum s | <= sum (fun x => `| s x |).
proof.
move => sum_s; rewrite ler_norml ler_sum_norm //= ler_oppl -sumN. 
apply ler_sum => /=; [smt()| exact summableN| exact summable_norm].
qed.

lemma summableM_bound (k : real) (s1 s2 : 'a -> real)  : 
  0%r < k => summable s1 => (forall x, `|s2 x| <= k) => summable (fun x => s1 x * s2 x).
proof.
move => k_gt0 [M sum_s1] bound_s2; exists (k * M) => J uniq_J. 
have R := sum_s1 _ uniq_J; rewrite -(ler_pmul2l k) // in R.
apply (ler_trans _ _ _ _ R) => {R}. rewrite BRA.mulr_sumr /=. 
apply Bigreal.ler_sum => /= x _. 
rewrite normrM Domain.mulrC. rewrite ler_wpmul2r /#.
qed.

lemma ler_sum_pos ['a] (s1 s2 : 'a -> real) : 
  (forall (x : 'a), 0%r <= s1 x <= s2 x) => summable s2 => sum s1 <= sum s2.
proof.
move => H sum_s2; apply: ler_sum => //; 1: smt().
by apply (summable_le_pos _ _ _ H).
qed.

(* the pattern [s a b] seems to be preferrable over the pattern [s(a,b)] *)
lemma sum_swap' (s : 'a -> 'b -> real) :
  summable (fun p : 'a * 'b => s p.`1 p.`2) => 
  sum (fun (a : 'a) => sum (fun (b : 'b) => s a b)) = 
  sum (fun (b : 'b) => sum (fun (a : 'a) => s a b)).
proof. exact (sum_swap (fun (ab : 'a * 'b) => s ab.`1 ab.`2)). qed.

(* this should probably replace dletE *)
lemma dletE (d : 'a distr) (F : 'a -> 'b distr) (E : 'b -> bool) : 
  mu (dlet d F) E = sum (fun x => mu1 d x * mu (F x) E).
proof.
rewrite dletE sum_swap' /=. 
  apply summable_cond; apply summable_pswap.
  rewrite (eq_summable _ 
     (fun (ab : 'a * 'b) => mass d ab.`1 * mass (F ab.`1) ab.`2)) //.
  apply summable_dlet. 
apply eq_sum => a /=; rewrite (muE _ E) -sumZ /= !massE.
apply eq_sum => b /=; smt().
qed.

import MRat.

(* same as muE, but using [mu1] rather than [mass] *)
lemma mu_mu1 (d : 'a distr) E : mu d E = sum (fun x => if E x then mu1 d x else 0%r).
proof. by rewrite muE; apply eq_sum => x /=; rewrite massE. qed.

lemma weightE (d : 'a distr) : weight d = sum (fun x => mu1 d x).
proof. by rewrite mu_mu1. qed.

(********** statistical distance ***************************************)

(* There are two common definitions of statistical distance between
(sub-)distributions (e.g. totoal variation distance) in the
literature: 

    1/2 * sum_x | mu1 d1 x - mu d2 x |

and 

    sup_E ( |mu d1 E - mu d2 E| )

The two notions agree whenever d1 and d2 have the same weight,
otherwise they potentially differ. For instance, when [d1 = dunit tt]
and [d2 = drat []] then the former definition yields 1/2 while the
latter definition yields 1. (See [example_sum] and [example_sup]
below.) *)

(* TOTHINK: Currently, we take the sup-based characterization as the
definition, but reason mostly about the sum-based one, switching the
roles mmay shift the weight-equivalence assumption to other lemmas *)

op sdist (d1 d2 : 'a distr) = flub (fun E => `|mu d1 E - mu d2 E|).

lemma sdist_sup (d1 d2 : 'a distr) E : 
  `|mu d1 E - mu d2 E| <= sdist d1 d2.
proof.
apply (flub_sup 1%r (fun E => `|mu d1 E - mu d2 E|)).
move => {E} E /=; smt(mu_bounded).
qed.
 
lemma sdist_max (d1 d2 : 'a distr) r :
  (forall E, `|mu d1 E - mu d2 E| <= r) => sdist d1 d2 <= r .
proof. exact ler_flub. qed.

(*----------------------------------------------------------------------------*)

lemma example_sum : 
    1%r/2%r * sum (fun x => `|mu1 (dunit tt) x - mu1 (drat []) x|) = 1%r/2%r.
proof.
rewrite (sumE_fin _ [tt]) //= BRA.big_cons BRA.big_nil /predT /=.
by rewrite dunitE dratE.
qed.

lemma example_sup : sdist (dunit tt) (drat []) = 1%r.
proof. 
apply ler_anti; split => [|_]; 1: by apply sdist_max => E; smt(mu_bounded).
apply (ler_trans _ _ _ _ (sdist_sup _ _ (pred1 tt))).
by rewrite dunit1E dratE divr0.
qed.

(*----------------------------------------------------------------------------*)

lemma sdist_ge0 (d1 d2 : 'a distr) : 0%r <= sdist d1 d2.
proof. 
have -> : 0%r = `|mu d1 pred0 - mu d2 pred0| by rewrite !mu0.
exact sdist_sup.
qed.

lemma sdistdd (d : 'a distr) : sdist d d = 0%r.
proof. 
apply ler_anti; rewrite sdist_ge0 /=. 
by apply sdist_max => E; rewrite subrr.
qed.

lemma sdist_triangle (d2 d1 d3 : 'a distr) : 
  sdist d1 d3 <= sdist d1 d2 + sdist d2 d3.
proof.
apply sdist_max => E.
apply (ler_trans (`| mu d1 E - mu d2 E | + `| mu d2 E - mu d3 E |)); 1: smt(mu_bounded).
by rewrite ler_add; apply/sdist_sup.
qed.

(*----------------------------------------------------------------------------*)

lemma sdist_dmap (d1 d2 : 'a distr) (F : 'a -> 'b) : 
  sdist (dmap d1 F) (dmap d2 F) <= sdist d1 d2.
proof. by apply sdist_max => E; rewrite !dmapE; exact sdist_sup. qed.


(*----------------------------------------------------------------------------*)

lemma sdist_sumE (d1 d2 : 'a distr) : 
  weight d1 = weight d2 =>
  sdist d1 d2 = 1%r/2%r * sum (fun x => `| mu1 d1 x - mu1 d2 x |).
proof.
rewrite /sdist => w_d1_d2.
pose F E := `|mu d1 E - mu d2 E|; pose f x := `|mu1 d1 x - mu1 d2 x|.
have sum_f : summable f by apply summable_sdist.
pose pos x := mu1 d1 x >= mu1 d2 x.
pose Sp := sum (fun x => if pos x then f x else 0%r).
pose Sn := sum (fun x => if !pos x then f x else 0%r).
rewrite (sum_split _ pos) // -/Sp -/Sn.
have eq_p_n : Sp = Sn. 
  rewrite /Sp /Sn /f.
  rewrite (eq_sum _ 
     (fun x => (if pos x then mu1 d1 x else 0%r) - (if pos x then mu1 d2 x else 0%r))); 1: smt().
  rewrite sumB; 1,2 : exact summable_mu1_cond.
  rewrite (eq_sum (fun x => if !pos x then `|mu1 d1 x - mu1 d2 x| else 0%r) 
    (fun x => (if ! pos x then mu1 d2 x else 0%r) - (if !pos x then mu1 d1 x else 0%r))); 1: smt().
  rewrite sumB /=; 1,2: exact summable_mu1_cond.
  rewrite RField.eqr_sub -!sum_split; 1,2: exact summable_mu1.
  by rewrite -!weightE.
suff : flub F = Sp by smt().
apply ler_anti; split => [|_]; last first. 
- apply (ler_trans (F pos)); 2: by apply (flub_sup 1%r); smt(mu_bounded).
  rewrite /Sp /F /f !mu_mu1 -sumB /=; 1,2: exact summable_mu1_cond.
  apply (ler_trans _ _ _ _ (ler_norm _)). 
  apply ler_sum; [smt()|apply/summable_cond/summable_sdist|].
  by apply/summableD;[|apply/summableN]; apply/summable_mu1_cond.
apply sdist_max => E.
rewrite (mu_split d1 E pos) (mu_split d2 E pos). 
have -> : forall (a b c d : real), a + b - (c + d) = (a - c) + (b - d) by smt().
rewrite !mu_mu1 -!sumB /=; 1..4: exact: summable_mu1_cond.
rewrite (eq_sum _ (fun x => if predI E pos x then mu1 d1 x - mu1 d2 x else 0%r)); 1: smt().
rewrite (eq_sum 
  (fun (x : 'a) => (if predI E (predC pos) x then mu1 d1 x else 0%r) - 
                   if predI E (predC pos) x then mu1 d2 x else 0%r)
  (fun x => if predI E (predC pos) x then mu1 d1 x - mu1 d2 x else 0%r)); 1: smt().
pose SEp := sum (fun (x : 'a) => if predI E pos x then mu1 d1 x - mu1 d2 x else 0%r).
pose SEn := sum (fun (x : 'a) => if predI E (predC pos) x then mu1 d1 x - mu1 d2 x else 0%r).
have ? : 0%r <= SEp /\ SEn <= 0%r. 
  split; 1: by apply ge0_sum; smt().
  apply/oppr_ge0. rewrite -sumN /=. by apply ge0_sum; smt().
suff : maxr SEp (-SEn) <= Sp by smt().
apply/ler_maxrP; split. 
- (apply ler_sum; 1: smt()); 2: exact/summable_cond.
  exact/summable_cond/norm_summable/summable_sdist.
- rewrite eq_p_n -sumN; (apply ler_sum; 1: smt()); 2: exact/summable_cond.
  exact/summableN/summable_cond/norm_summable/summable_sdist.
qed.

(*----------------------------------------------------------------------------*)

lemma sdist_dlet (d1 d2 : 'a distr) (F : 'a -> 'b distr) : 
  weight d1 = weight d2 => weight (dlet d1 F) = weight (dlet d2 F) => 
   sdist (dlet d1 F) (dlet d2 F) <= sdist d1 d2.
proof.
move => eq_w_d eq_w_dF; rewrite !sdist_sumE // ler_pmul2l 1:/#.
have sum_dF : forall d y, summable (fun (x : 'a) => mu1 d x * mu1 (F x) y).
  by move => d y; apply (summableM_bound 1%r) => //; [exact summable_mu1| smt(mu_bounded)].
have H : forall y, `|mu1 (dlet d1 F) y - mu1 (dlet d2 F) y| <= 
                    sum (fun x => `| mu1 d1 x - mu1 d2 x | * mu1 (F x) y).
  move => y. rewrite !dletE -sumB /=; 1,2: exact: sum_dF.
  apply (ler_trans _ _ _ (norm_sum_sum _ _) _) => /=. 
    apply summableD. apply sum_dF. apply/summableN/sum_dF.
  rewrite ler_eqVlt; left; apply eq_sum => /= x; smt(mu_bounded).
have I : forall x, 0%r <= sum (fun y => `|mu1 d1 x - mu1 d2 x| * mu1 (F x) y) <= `|mu1 d1 x - mu1 d2 x|.
  move => x. split => [|_]; 1: by apply ge0_sum; smt(mu_bounded).
  rewrite sumZ -weightE; smt(mu_bounded ler_pimulr).
apply (ler_trans _ _ _ _ (ler_sum_pos _ _ I _)); 2: by apply summable_sdist. 
have sum_I := summable_le_pos _ _ _ I; 1: by apply summable_sdist.
have sum_p : summable (fun (p : 'a * 'b) => `|mu1 d1 p.`1 - mu1 d2 p.`1| * mu1 (F p.`1) p.`2).
  apply (summableM_dep (fun x => `|mu1 d1 x - mu1 d2 x|) (fun x y => mu1 (F x) y)). 
    exact summable_sdist.
  rewrite /(\o). exists 1%r => x J uniq_J. 
  rewrite (BRA.eq_bigr _ _ (mu1 (F x))) => [y /= _|]; 1: by rewrite ger0_norm // ge0_mu. 
  by rewrite -mu_mem_uniq. 
rewrite sum_swap' //=. 
apply (ler_trans _ _ _ (ler_sum _ _ H _ _)) => //; 1: by apply summable_sdist. 
  by move/summable_pswap/summable_pair_sum : sum_p. 
qed.

(*----------------------------------------------------------------------------*)

lemma sdist_dprod2r (d1 d2 : 'a distr) (d : 'b distr) : 
  weight d1 = weight d2 => 
  sdist (d1 `*` d) (d2 `*` d) = sdist d1 d2 * weight d.
proof.
move => eq_w; rewrite !sdist_sumE // ?weight_dprod ?eq_w // -(mulrA (1%r/2%r)).
congr. rewrite mulrC -sumZ /= sum_pair; 1: exact summable_sdist.
apply eq_sum => x /=.
rewrite (eq_sum _ (fun b => `|mu1 d1 x - mu1 d2 x| * mu1 d b)) => [b /=|].
+ rewrite !dprod1E; smt(mu_bounded).
by rewrite sumZ mulrC -weightE.
qed.

lemma sdist_dprodC_aux (dl1 dl2 : 'a distr) (dr1 dr2 : 'b distr) :
  sdist (dl1 `*` dr1) (dl2 `*` dr2) <= sdist (dr1 `*` dl1) (dr2 `*` dl2).
proof.
apply sdist_max => E; rewrite (dprodC dl1 dr1) (dprodC dl2 dr2) !dmapE.
exact: sdist_sup.
qed.

lemma sdist_dprodC (dl1 dl2 : 'a distr) (dr1 dr2 : 'b distr) :
  sdist (dl1 `*` dr1) (dl2 `*` dr2) = sdist (dr1 `*` dl1) (dr2 `*` dl2).
proof. by apply ler_anti; rewrite !sdist_dprodC_aux. qed.

lemma sdist_dprod (dl1 dl2 : 'a distr) (dr1 dr2 : 'b distr) :
  weight dl1 = weight dl2 => weight dr1 = weight dr2 =>
  sdist (dl1 `*` dr1) (dl2 `*` dr2) <= sdist dl1 dl2 + sdist dr1 dr2.
proof.
move => eq_wl eq_wr. 
have L := sdist_triangle (dl2 `*` dr1) (dl1 `*` dr1) (dl2 `*` dr2).
apply (ler_trans _ _ _ L); rewrite (sdist_dprodC dl2) !sdist_dprod2r //.
rewrite ler_add; smt(mu_bounded sdist_ge0 ler_pimulr).
qed.

lemma sdist_dlist (d1 d2 : 'a distr) n : 
  weight d1 = weight d2 => 0 <= n => 
  sdist (dlist d1 n) (dlist d2 n) <= n%r * sdist d1 d2.
proof.
move => eq_w; elim: n => [|n ? IHn]; 1: by rewrite !dlist0 // sdistdd.
rewrite !dlistS //. 
apply (ler_trans _ _ _ (sdist_dmap _ _ _)).
apply (ler_trans _ _ _ (sdist_dprod _ _ _ _ _ _)) => //; 2: smt().
by rewrite !weight_dlist // eq_w.
qed.

(*----------------------------------------------------------------------------*)

(* Experiments *)

theory T.

type a.
op d1, d2 : a distr.

module type Distinguisher = { 
  proc guess (x : a) : bool
}.

module Sample (A : Distinguisher) = { 
  proc main(b : bool) = {
    var x,r;
    x <- witness;
    if (!b) { x <$ d1; } else { x <$ d2; }
    r <@ A.guess(x);
    return r;
  }
}.

lemma plik &m z (A <: Distinguisher) x' : 
  Pr[A.guess(x') @ &m : res = z] = 
  mu1 (mk (fun b => Pr[A.guess(x') @ &m : res = b])) z.
proof.
byphoare (: x = x' ==> _) => //; proc*.
admit.
qed.

lemma bar (A <: Distinguisher) &m y : 
    Pr [Sample(A).main(false) @ &m : res = y] = 
    mu1 (dlet d1 (fun x => (mk (fun r => Pr [A.guess(x) @ &m : res = y])))) y.
proof. 
byphoare (_ : b = false ==> _) => //. proc; rcondt 2; 1:by auto.

(* provable ? *) abort.

(* Justified by semantic argument using sdist_dlet *)
axiom foo (A <: Distinguisher) &m : 
  `| Pr[Sample(A).main(false) @ &m : res] - Pr[Sample(A).main(true) @ &m : res] | <=  sdist d1 d2.

end T.
