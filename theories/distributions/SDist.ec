require import AllCore List FSet Distr DProd DList StdBigop StdOrder Hybrid.
(*---*) import Bigreal RealSeries RealOrder RField BRA MRat.

require PROM.

(********** preliminaries (to move) ***************************************)

lemma normrZ (x y : real) : 0%r <= x => `| x * y | = x * `| y |. proof. smt(). qed.

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

(* same as muE, but using [mu1] rather than [mass] *)
lemma mu_mu1 (d : 'a distr) E : mu d E = sum (fun x => if E x then mu1 d x else 0%r).
proof. by rewrite muE; apply eq_sum => x /=; rewrite massE. qed.

lemma weightE (d : 'a distr) : weight d = sum (fun x => mu1 d x).
proof. by rewrite mu_mu1. qed.

lemma const_weight_dlet r (d : 'a distr) (F : 'a -> 'b distr) : 
  (forall x, weight (F x) = r) => weight (dlet d F) = r * weight d.
proof.
move => wF; rewrite !dletE (eq_sum _ (fun x => r * mu1 d x)) => [x /=|].
  by rewrite wF mulrC. 
by rewrite sumZ -weightE.
qed.


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
apply (ler_trans (`| mu d1 E - mu d2 E | + `| mu d2 E - mu d3 E |)).
  smt(mu_bounded).
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
     (fun x => (if pos x then mu1 d1 x else 0%r) - 
               (if pos x then mu1 d2 x else 0%r))); 1: smt().
  rewrite sumB; 1,2 : exact summable_mu1_cond.
  rewrite (eq_sum (fun x => if !pos x then `|mu1 d1 x - mu1 d2 x| else 0%r) 
    (fun x => (if ! pos x then mu1 d2 x else 0%r) - 
              (if !pos x then mu1 d1 x else 0%r))); 1: smt().
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
rewrite (eq_sum _ 
  (fun x => if predI E pos x then mu1 d1 x - mu1 d2 x else 0%r)); 1: smt().
rewrite (eq_sum 
  (fun (x : 'a) => (if predI E (predC pos) x then mu1 d1 x else 0%r) - 
                    if predI E (predC pos) x then mu1 d2 x else 0%r)
  (fun x => if predI E (predC pos) x then mu1 d1 x - mu1 d2 x else 0%r)); 1: smt().
pose SEp := sum (fun (x : 'a) => 
                 if predI E pos x then mu1 d1 x - mu1 d2 x else 0%r).
pose SEn := sum (fun (x : 'a) => 
                 if predI E (predC pos) x then mu1 d1 x - mu1 d2 x else 0%r).
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
  move => d y; apply (summableM_bound 1%r) => //; first exact summable_mu1.
  smt(mu_bounded).
have I : forall x, 0%r <= sum (fun y => 
    `|mu1 d1 x - mu1 d2 x| * mu1 (F x) y) <= `|mu1 d1 x - mu1 d2 x|.
+ move => x. split => [|_]; 1: by apply ge0_sum; smt(mu_bounded).
  rewrite sumZ -weightE; smt(mu_bounded ler_pimulr).
apply (ler_trans _ _ _ _ (ler_sum_pos _ _ I _)); 2: by apply summable_sdist. 
have sum_p : summable (fun (p : 'a * 'b) => 
    `|mu1 d1 p.`1 - mu1 d2 p.`1| * mu1 (F p.`1) p.`2).
+ apply (summableM_dep (fun x => `|mu1 d1 x - mu1 d2 x|) (fun x y => mu1 (F x) y)).
    exact summable_sdist.
  rewrite /(\o). exists 1%r => x J uniq_J. 
  rewrite (eq_bigr _ _ (mu1 (F x))) => [y /= _|]; 1: by rewrite ger0_norm // ge0_mu.
  by rewrite -mu_mem_uniq. 
rewrite sum_swap' //=; apply ler_sum => [y /=| |]; 2: exact summable_sdist.
+ rewrite !dletE -sumB /=; 1,2: exact: sum_dF.
  apply (ler_trans _ _ _ (norm_sum_sum _ _) _) => /=.
    by apply summableD;[apply sum_dF|apply/summableN/sum_dF].
  rewrite ler_eqVlt; left; apply eq_sum => /= x; smt(mu_bounded).
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

(* Generic Distinguishers and their output distributions *)
abstract theory A.
type a, b. 

module type Distinguisher = { 
  proc guess (x : a) : b
}.

lemma uniq_big_res (A <: Distinguisher) &m x' (bs : b list) : 
  uniq bs =>
  big predT (fun b => Pr[A.guess(x') @ &m : res = b]) bs = 
  Pr[A.guess(x') @ &m : res \in bs].
proof.
elim: bs => [_|b bs IHbs /= [bNbs uq_bs]].
  by rewrite big_nil; byphoare => //; hoare; auto.
by rewrite big_cons {1}/predT /= IHbs // Pr[mu_disjoint] /#.
qed.

lemma adv_isdistr (A <: Distinguisher) &m x' : 
    isdistr (fun b => Pr[A.guess(x') @ &m : res = b]).
proof.
split => [/= y|bs uq_bs]; 1: by byphoare.
by rewrite (uniq_big_res A &m) //; byphoare. 
qed.

lemma adv_mu1 (A <: Distinguisher) &m z x' : 
  Pr[A.guess(x') @ &m : res = z] = 
  mu1 (mk (fun b => Pr[A.guess(x') @ &m : res = b])) z.
proof.
by rewrite -massE muK //; exact (adv_isdistr A).
qed.

module S = {
  proc sample (d : b distr) = {
    var r; 
  
    r <$ d;
    return r;
  }
}.

lemma sampleE d' &m a : 
    Pr[S.sample(d') @ &m : res = a] = mu1 d' a.
proof.
by byphoare (: d = d' ==> _) => //; proc; rnd; auto.
qed.

end A.

(*----------------------------------------------------------------------------*)

(* Boolean distinguishers for distributions *)

abstract theory T. 
type a. 

clone import A with
  type a <- a,
  type b <- bool.

clone import DLetSampling as DLS with
  type t <- a,
  type u <- bool.

(* Part 1 : Sampling game: the distinguiser is given a sampled value *)

module Sample (A : Distinguisher) = { 
  proc main(d : a distr) = {
    var x,r; 

    x <$ d;
    r <@ A.guess(x);
    return r;
  }
}.

lemma Sample_dlet (A <: Distinguisher) &m d' : 
    Pr [Sample(A).main(d') @ &m : res] = 
    mu1 (dlet d' (fun x => (mk (fun z => Pr [A.guess(x) @ &m : res=z])))) true.
proof. 
pose F := (fun x => (mk (fun r => Pr [A.guess(x) @ &m : res = r]))).
have -> : Pr[Sample(A).main(d') @ &m : res] = 
          Pr[SampleDep.sample(d',F) @ &m : res].
  byequiv => //; proc. 
  seq 1 1 : ((glob A){1} = (glob A){m} /\ du{2} = F /\ x{1} = t{2}). 
    by rnd; skip; smt(). (* rnd; auto raises anomaly *)
  transitivity{2} {u <@ S.sample(du t); } 
    ((glob A){1} = (glob A){m} /\ du{2} = F /\ x{1} = t{2} ==> r{1} = u{2}) 
    (={du,t} ==> ={u}); 1,2: smt(); 2: by inline*;auto.
  call (: d{2} = (F x){1} /\ (glob A){1} = (glob A){m} ==> ={res}).
  bypr (res{1}) (res{2}); 1:smt(). 
  move => &1 &2 a [-> eq_globA]; rewrite sampleE -(adv_mu1 A). 
  byequiv (: ={x,glob A} ==> ={res}) => //; 1: by sim. 
  by move: F => F; auto. (* abstracting over F avoids anomaly *)
have -> : Pr[SampleDep.sample(d', F) @ &m : res] = 
          Pr[SampleDLet.sample(d', F) @ &m : res].
  byequiv => //; conseq SampleDepDLet. by move: F; auto.
byphoare (: dt = d' /\ du = F ==> _) => //; proc. 
by rnd; skip; move => &1 /= [-> ->]; apply mu_eq; case.
qed.

(* TOTHINK: This proof relies on an explicit enumeration of [bool].
   It should be possible to generalize the result to arbitary types *)
lemma distinguisher_ll (A <: Distinguisher) &m x : 
  islossless A.guess => 
  is_lossless (mk (fun (z : bool) => Pr[A.guess(x) @ &m : res = z])).
proof.
move => A_ll; rewrite /F /is_lossless muE {1}/predT /=. 
have <- : Pr[A.guess(x) @ &m : res = true \/ res = false] = 1%r. 
  by byphoare => //; conseq (:_ ==> true) => // /#.  
rewrite (eq_sum _ (fun (z : bool) => Pr[A.guess(x) @ &m : res = z])) => [z /=|].
  by rewrite muK; 1: exact: (adv_isdistr A).
rewrite (sumE_fin _ [true; false]) // 1:/# !big_cons big_nil /predT/=.
by rewrite Pr[mu_disjoint] 1:/#. 
qed.

lemma adv_sdist (A <: Distinguisher) &m d1 d2 : 
  weight d1 = weight d2 => islossless A.guess =>
  `| Pr[Sample(A).main(d1) @ &m : res] - Pr[Sample(A).main(d2) @ &m : res] | 
  <=  sdist d1 d2.
proof.
move => eq_w a_ll; rewrite !(Sample_dlet A).
pose F x := mk (fun (z : bool) => Pr[A.guess(x) @ &m : res = z]).
have WF : forall x, weight (F x) = 1%r by move => x; exact (distinguisher_ll A).
apply (ler_trans _ _ _ (sdist_sup _ _ _) (sdist_dlet _ _ F _ _)) => //.
by rewrite !(const_weight_dlet 1%r).
qed.


(* Part 2 : The distinguiser is given oracle acces to the distribution *)

module type Oracle = {
  proc get() : a
}.

module type Oracle_i = {
  include Oracle
  proc init(d : a distr) : unit
}.

module type Adversary (O : Oracle) = { 
  proc main() : bool
}.

module Count (O : Oracle_i) = { 
  var n : int
  
  proc init (d' : a distr) = {
    n <- 0;
    O.init(d');
  }

 proc get() = { 
    var r;

    n <- n + 1;
    r <@ O.get();
    return r;
  }
}.

(* main distringuisher game *)
module Game(A : Adversary, O:Oracle_i) = {
  module CO = Count(O)

  proc main(d) = {
    var r;

    CO.init(d);
    r <@ A(CO).main();
    return r;
  }
}.

(* adversary of reduction to sampling game *)
module B1(A : Adversary) = {
  var x' : a

  module Ox = {
    proc init(x : a) = { x' <- x; }
    proc get() = {return x'; }
  }

  proc guess(x : a) = {
    var r;

    Ox.init(x);
    r <@ A(Ox).main();
    return r;
  }
}.


(* always sample *)
module Os : Oracle_i = {
  var d : a distr
  proc init (d' : a distr) = { d <- d'; }
  proc get () = { var r; r <$ d; return r; }
}.

section. (* Reduction from single oracle call to sampling game *)

declare module A : Adversary {B1,Os,Count}.

axiom A_ll : forall (O <: Oracle{A}), islossless O.get => islossless A(O).main.

(* global variables for eager/lazy proof *)
local module Var = { 
  var x : a  
  var b : bool 
  var d : a distr
}.

(* sample once *)
local module O1 : Oracle_i = {
  proc init (d' : a distr) = { Var.x <$ d'; }
  proc get () = { return Var.x; }
}.

(* conditional sampling - eager *)
local module O1e : Oracle_i = {
  proc init (d' : a distr) = { 
    Var.x <- witness;
    Var.d <- d'; 
    Var.b <- true; 
    if (Var.b) Var.x <$ Var.d ; 
  }

  proc get () = { Var.b <- false; return Var.x; }
}.

(* conditional sampling - lazy *)
local module O1l = {
  var d : a distr

  proc init(d') = { 
    Var.x <- witness;
    Var.d <- d'; 
    Var.b <- true; 
  }
  proc get() = { 
    if (Var.b) Var.x <$ Var.d; 
    Var.b <- false ; 
    return Var.x;
  }
}.

(* "Game" with conditional resampling at the end *)
local module Gr(O : Oracle_i) = {
  module CO = Count(O)

  proc main(d) = { 
    var r;

    CO.init(d);
    r <@ A(CO).main();
    if (Var.b) Var.x <$ Var.d;
    return r;
  }
}.

lemma sdist_oracle1 &m (d1 d2 : a distr) : 
   is_lossless d1 => is_lossless d2 =>
  (forall (O <: Oracle_i{Count,A}), 
     hoare[ A(Count(O)).main : Count.n = 0 ==> Count.n <= 1]) =>
  `| Pr[Game(A,Os).main(d1) @ &m : res] - Pr[Game(A,Os).main(d2) @ &m : res] | 
  <= sdist d1 d2.
proof.
move => d1_ll d2_ll A_bound. 
suff H : forall d', is_lossless d' =>
  Pr[Game(A, Os).main(d') @ &m : res] = Pr [Sample(B1(A)).main(d') @ &m : res].
+ rewrite !H ?d1_ll ?d2_ll; apply (adv_sdist (B1(A))); 1: by rewrite d1_ll d2_ll.
  by islossless; apply (A_ll (<: B1(A).Ox)); islossless.
move => d' d'_ll.
suff <-: Pr[Game(A, O1).main(d') @ &m : res] = Pr[Game(A, Os).main(d') @ &m : res].
+ byequiv => //. proc; inline *; wp. 
  by call(: Var.x{1} = B1.x'{2}); [proc; inline *|]; auto. 
byequiv => //.
transitivity Game(A,O1e).main 
  (={arg,glob A} /\ d{1} = d' ==> ={res}) 
  (={arg,glob A} /\ d{1} = d' ==> ={res}); 1,2: smt().
  by proc; inline *; rcondt{2} 7; auto; call(: ={Var.x}); 1: sim; auto => />.
transitivity Gr(O1l).main 
  (={arg,glob A} /\ d{1} = d' ==> ={res}) 
  (={arg,glob A} /\ d{1} = d' ==> ={res}); 1,2: smt().
  proc; inline *.
  seq 6 6 : (={glob Var, glob A}); 1: by auto.
  eager (H : if (Var.b) Var.x <$ Var.d; ~  if (Var.b) Var.x <$ Var.d; 
    : ={glob Var} ==> ={glob Var} )
    : (={glob A,glob Var} ) => //; 1: by sim. 
  eager proc H (={glob Var}) => //; 2: by sim.
  proc*; inline *; rcondf{2} 6; [ by auto | by sp; if; auto].
proc; inline*. 
seq 7 5 : (={r} /\ Var.d{1} = d'); last by if{1}; auto => />.
conseq (_ : _ ==> Count.n{1} <= 1 /\ Count.n{2} <= 1 => 
                  ={Count.n,r} /\ Var.d{1} = d')
       (_ : _ ==> Count.n <= 1) (_ : _ ==> Count.n <= 1); 1: smt().
+ by call (A_bound O1l); auto.
+ by call (A_bound Os); auto.
call (: 2 <= Count.n, 
        ={Count.n} /\ Var.d{1} = Os.d{2} /\ 0 <= Count.n{1} /\ 
        (Var.b <=> Count.n = 0){1} /\ Os.d{2} = d', 
        Var.d{1} = Os.d{2} /\ Os.d{2} = d' /\ 2 <= Count.n{2}).
- move=> O; exact (A_ll O).
- proc; inline *; sp; if{1}; 1: by wp; rnd; auto => />. 
  auto => />. smt().
- by move => ? _; proc; inline*; sp; if; auto.
- by move => ?; proc; inline*; auto => /> /#. 
- by auto => />; smt().
qed.

end section.

(* Reduction from n oracle calls to single oracle call *)
abstract theory N1.

(* We need operators, because we need to define modules that use them *)
op d1,d2 : a distr.
axiom d1_ll : is_lossless d1.
axiom d2_ll : is_lossless d2.

op N : { int | 0 < N } as N_pos.

section. 

declare module A : Adversary {B1,Os,Count}.

axiom A_ll : forall (O <: Oracle{A}), islossless O.get => islossless A(O).main.

axiom A_bound : (forall (O <: Oracle_i{A,Count}), 
  hoare[ A(Count(O)).main : Count.n = 0 ==> Count.n <= N]).

local clone Hybrid as Hyb with
  type input <- unit,
  type output <- a,
  type inleaks <- unit,
  type outleaks <- unit,
  type outputA <- bool,
  op q <- N,
  lemma q_pos <- N_pos.

local module Ob : Hyb.Orclb = {

  proc leaks () = { return (); }
  
  proc orclL () = {
    var r;

    r <$ d1;
    return r;
  }

  proc orclR () = {
    var r;

    r <$ d2;
    return r;
  }
}.

(* : Hyb.AdvOrclb *)
local module B (Ob : Hyb.Orclb) (O : Hyb.Orcl) = {
  module O' : Oracle = {
    proc init(d : a distr) = {}
    proc get = O.orcl
  }
    
  proc main() : bool = {
    var r; 
    
    (* Adding counting here simplifies the proof of the bound
      for Hyb.AdvCount(B(Ob, Hyb.OrclCount(O))).main below *)
    Count.n <- 0; 
    r <@ A(Count(O')).main();
    return r;
  }
}.

(* It would be nice to replace [Game(C,Os)] with [Game(Hyb.HybOrcl(Ob,O))] 
   for some Ob/O. However, HybOrcl does not have an init, so we need a module 
   an do the initialization in [main] *)
local module C (O : Oracle) = {
  var k, i : int

  module O' = {
    proc get () = {
      var x; 
      if   (k < i) x <$ d1;
      elif (i = k) x <@ O.get();
      else         x <$ d2;
      i <- i + 1;
      return x;
    }
  }

  proc main() = { 
    var r;

    k <$ [0..N-1];
    i <- 0;
    r <@ A(O').main();
    return r;
  } 
}.

local lemma Osd1_Hyb &m :
   Pr[Game(A, Os).main(d1) @ &m : res] = Pr[ Hyb.Ln(Ob, B).main() @ &m : res ].
proof.
byequiv => //; proc; inline *; auto. 
call (: Os.d{1} = d1); [by proc; inline*; auto| by auto].
qed.

local lemma Osd2_Hyb &m :
   Pr[Game(A, Os).main(d2) @ &m : res] = Pr[ Hyb.Rn(Ob, B).main() @ &m : res ].
proof.
byequiv => //; proc; inline *; auto. 
call (: Os.d{1} = d2); [by proc; inline*; auto| by auto].
qed.

local lemma A_bound' (O <: Oracle_i{A,Count}) : 
  hoare [ Game(A,O).main : true ==> Count.n <= N ].
proof.
by proc; inline *; sp; call (A_bound O); call(: true); auto.
qed.

lemma sdist_oracleN &m : 
  `| Pr[Game(A,Os).main(d1) @ &m : res] - Pr[Game(A,Os).main(d2) @ &m : res] | 
  <= N%r * sdist d1 d2.
proof.
rewrite -ler_pdivr_mull -?normrZ; 1,2: smt(N_pos). 
rewrite Osd1_Hyb Osd2_Hyb. 
have /= <- := Hyb.Hybrid_restr (<: Ob) (<: B) _ _ _ _ _ &m (fun _ _ _ r => r).
- move => O; proc; inline *; sp; wp. 
  conseq (: Hyb.Count.c = Count.n) (: Count.n = 0 ==> Count.n <= N) => //. 
    by call (A_bound (<: B(Ob, Hyb.OrclCount(O)).O')).
  call (: Hyb.Count.c = Count.n) => //.
  by proc; inline *; auto; call(: true); auto.
- by islossless.
- islossless; exact d1_ll.
- islossless; exact d2_ll.
- move => Ob LR *; islossless. 
  by apply (A_ll (<: Count(B(Ob, LR).O'))); islossless.
have -> : Pr[Hyb.HybGame(B, Ob, Hyb.L(Ob)).main() @ &m : res] = 
          Pr[Game(C, Os).main(d1) @ &m : res].
  byequiv => //; proc; inline*; auto. 
  call (: Hyb.HybOrcl.l0{1} = C.k{2} /\ Hyb.HybOrcl.l{1} = C.i{2} /\ 
          Os.d{2} = d1); last by auto.
  proc; inline *; sp.
  if; [smt() | by auto |].
  if; [smt()| by auto | by auto].
have -> : Pr[Hyb.HybGame(B, Ob, Hyb.R(Ob)).main() @ &m : res] = 
          Pr[Game(C, Os).main(d2) @ &m : res].
  byequiv => //; proc; inline*; auto. 
  call (: Hyb.HybOrcl.l0{1} = C.k{2} /\ Hyb.HybOrcl.l{1} = C.i{2} /\ 
          Os.d{2} = d2); last by auto.
  proc; inline *; sp.
  if; [smt() | by auto |].
  if; [smt()| by auto | by auto].
apply (sdist_oracle1 C).
- move => O O_ll; islossless. 
  + apply (A_ll (<: C(O).O')); islossless. exact: d1_ll. exact: d2_ll.
  + rewrite DInterval.weight_dinter. smt(N_pos).
- exact: d1_ll.
- exact: d2_ll.
move => O; proc.
call(: if C.i <= C.k then Count.n = 0 else Count.n = 1). 
- proc; if; 1: (by auto; smt()); if; 2: by auto; smt().
  inline *; auto. call(: true) => //. auto; smt().
auto; smt(DInterval.supp_dinter).
qed.

end section.

end N1.

abstract theory ROM.

import SmtMap.

type in_t. (* TODO: rename "a" to something more meaningful *)
op d1, d2 : a distr.
axiom d1_ll : is_lossless d1.
axiom d2_ll : is_lossless d2.
op N : { int | 0 < N } as N_pos.

clone PROM.FullRO as R1 with 
  type in_t <- in_t, 
  type out_t <- a, 
  type d_in_t <- unit,
  type d_out_t <- bool,
  op dout <- fun _ => d1.

clone PROM.FullRO as R2 with 
  type in_t <- in_t, 
  type out_t <- a, 
  type d_in_t <- unit,
  type d_out_t <- bool,
  op dout <- fun _ => d2.

module O1 = R1.RO.
module O2 = R2.RO.

(* This allows us to PROM rather then ROM, and the former has better
infrastructure (e.g., for splitting into muliple oracles *)
module type Distinguisher (O : R1.RO) = {
  proc distinguish(_ : unit) : bool {O.get}
}.

module Wrap (O : R1.RO) : R1.RO = {
  var dom : in_t fset

  proc init() = { 
    dom <- fset0 ; 
    O.init(); 
  }
  proc get(x) = { 
    var r;
    dom <- dom `|` fset1 x; 
    r <@ O.get(x); 
    return r;
  }
  
  (* never called by our distinguisher *)
  proc set = O.set
  proc sample = O.sample
  proc rem = O.rem
}.

section.

declare module D : Distinguisher {Os, O1,O2, Count, B1, Wrap}.

axiom D_ll : forall (O <: R1.RO{D}), 
  islossless O.get => islossless D(O).distinguish.

local module Cache (O : Oracle) : R1.RO = {
  var m : (in_t,a) fmap 

  proc init () = { m <- empty; }

  proc get(i) = {
    var x; 

    if (! i \in m) {
      x <@ O.get();
      m.[i] <- x;
    }
    return oget (m.[i]);
  }

  (* never called by our distinguisher *)
  proc set(x : in_t, y : a) = {}
  proc sample(x: in_t) = {}
  proc rem(x: in_t) = {}
}.

local module A (O : Oracle) = {
  module O' = Wrap(Cache(O))
 
  proc main () = {
     var r;

     O'.init();
     r <@ D(O').distinguish();
     return r;
  }
}.

local clone N1 as N1 with
  op d1 <- d1,
  op d2 <- d2,
  axiom d1_ll <- d1_ll,
  axiom d2_ll <- d2_ll,
  op N <- N,
  axiom N_pos <- N_pos.

lemma sdist_ROM  &m : 
 (forall (O <: R1.RO{Wrap,D}), 
   hoare [ D(Wrap(O)).distinguish : Wrap.dom = fset0 ==> card Wrap.dom <= N]) =>
  `| Pr [R1.MainD(D,O1).distinguish() @ &m : res] - 
     Pr [R1.MainD(D,O2).distinguish() @ &m : res] |
  <= N%r * sdist d1 d2.
proof.
move => D_bound. 
have -> : Pr[R1.MainD(D,O1).distinguish() @ &m : res] = 
          Pr[Game(A,Os).main(d1) @ &m : res].
- byequiv => //; proc; inline *; wp.
  call(: ={m}(O1,Cache) /\ Os.d{2} = d1); last by auto.
  proc; inline *; sp.
  if{2}; [by rcondt{1} 2; auto| rcondf{1} 2; auto; smt(d1_ll)].
have -> : Pr[R1.MainD(D,O2).distinguish() @ &m : res] = 
          Pr[Game(A,Os).main(d2) @ &m : res].
- byequiv => //; proc; inline *; wp.
  call(: ={m}(O2,Cache) /\ Os.d{2} = d2); last by auto.
  proc; inline *; sp.
  if{2}; [by rcondt{1} 2; auto| rcondf{1} 2; auto; smt(d2_ll)].
apply (N1.sdist_oracleN A _ _ &m). 
- move=> O get_ll. islossless. apply (D_ll (<: Wrap(Cache(O)))).
  islossless. 
move => O; proc; inline *; sp.
conseq (: Count.n <= card Wrap.dom /\ fdom Cache.m = Wrap.dom) 
       (: Wrap.dom = fset0 ==> card Wrap.dom <= N); 1,2: smt(). 
- by call (D_bound (<: Cache(Count(O)))).
call (: Count.n <= card Wrap.dom /\ fdom Cache.m = Wrap.dom); last first.
  by auto; smt(fcards0 fdom0).
proc; inline*; wp; sp; if. 
- auto; call(: true); auto => /> &1 cnt_n x_cache a.
  split; last by rewrite fdom_set.
  by rewrite !fcardU fsetI1 !mem_fdom x_cache /= fcards0 fcard1 /#.
- auto => /> &1 cnt_n x_cache. 
  split; last by apply/fsetP => x; rewrite !inE !mem_fdom /#.
  rewrite fcardU fcard1 fsetI1 mem_fdom x_cache /=.
  smt (fcardU fcard1 fcard_ge0).
qed.

end section.

end ROM.

end T.
