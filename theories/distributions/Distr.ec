(*
 * This file contains a formalization of (discrete) distributions
 *
 * [mu1 d x]       : probability of the value [x] in the distribution [d].
 * [mu d E]        : probability of the event [E] in the distribution [d].
 * [x \in d]       : [x] is in the support of [d].
 * [x \notin d]    : [x] isn't in the support of [d].
 * [is_lossless d] : the distribution [d] is lossless.
 * [is_full d]     : the distribution [d] is full.
 * [is_uniform d]  : all elements in d have the same probability.
 * [is_funiform d] : all elements have the same probability.
 *
 * Given a distribution named distr we use the following naming conventions:
 *
 * - distr1E    : equation defining mu1
 * - distrE     : equation defining mu
 * - supp_distr : equation defining the support (i.e of \in)
 * - distr_ll   : lemma on is_lossless
 * - distr_fu   : lemma on is_full
 * - distr_uni  : lemma on is_uniform
 * - distr_funi : lemma on is_funiform
 *)

(* -------------------------------------------------------------------- *)
require import AllCore List Binomial.
require import Ring StdRing StdOrder StdBigop Discrete.
require import RealFun RealSeq RealSeries RealFLub.
(*---*) import IterOp Bigint Bigreal Bigreal.BRA.
(*---*) import IntOrder RealOrder RField.
require import Finite FinType.

pragma +implicits.

(* -------------------------------------------------------------------- *)
(* We use the [mass] function to state axioms about distributions and
define the [mu] function. Since [mass d x = mu1 d x] and lemmas about
[mu] also apply to [mu1], user-oriented lemmas should use [mu1]
exclusively and should not use [mass]. *)

type 'a distr = 'a Pervasive.distr.

op mass ['a] : 'a distr -> 'a -> real.

axiom mu_mass ['a] (d : 'a distr) (E : 'a -> bool):
  mu d E = sum (fun x => if E x then mass d x else 0%r).

abbrev mu1 (d:'a distr) x = mu d (pred1 x).

lemma massE ['a] (d : 'a distr) x : mass d x = mu1 d x.
proof.
rewrite mu_mass (@sumE_fin _ [x]) ?big_seq1 //=.
by move=> y @/pred1; case: (y = x).
qed.

lemma muE ['a] (d : 'a distr) (E : 'a -> bool):
  mu d E = sum (fun x => if E x then mu1 d x else 0%r).
proof. by rewrite mu_mass; apply eq_sum => x /=; rewrite massE. qed.

(* -------------------------------------------------------------------- *)
op mk : ('a -> real) -> 'a distr.

inductive isdistr (m : 'a -> real) =
| Distr of
       (forall x, 0%r <= m x)
     & (forall s, uniq s => big predT m s <= 1%r).

lemma isdistr_summable_equiv (m : 'a -> real) :
  isdistr m <=> (forall x, 0%r <= m x) /\ summable m /\ sum m <= 1%r.
proof.
rewrite/bounded. split => [ [ * ] | [ ? [ * ] ] ]; last first.
- split; 1: assumption.
  move => ? ?. apply (ler_trans (sum m)) => //.
  by apply ler_big_sum => //. 
have sumM : summable m.
- exists 1%r.
  have <- : (fun i => `|m i|) = m; smt().
do 2 ! (split => //).
by apply (lerfin_sum sumM).
qed.

lemma eq_isdistr (d1 d2 : 'a -> real) :
  d1 == d2 => isdistr d1 = isdistr d2.
proof. by move=> /fun_ext=> ->. qed.

lemma ge0_isdistr (d : 'a -> real) x : isdistr d => 0%r <= d x.
proof. by case=> + _; apply. qed.

lemma le1_isdistr (d : 'a -> real) x : isdistr d => d x <= 1%r.
proof. by case=> _ /(_ [x] _) //; rewrite big_seq1. qed.

lemma le1_sum_isdistr (d : 'a -> real) s :
  isdistr d => uniq s => big predT d s <= 1%r.
proof. by case=> _; apply. qed.

axiom distrW (P : 'a distr -> bool):
  (forall m, isdistr m => P (mk m)) => forall d, P d.

axiom massK (m : 'a -> real): isdistr m => mass (mk m) = m.

lemma muK (m : 'a -> real) x : isdistr m => mu1 (mk m) x = m x. 
proof. by move=> dis_m; rewrite -massE massK. qed.

(* The abbeviation [mu1] is always fully applied, and EC uses eta if
necessary. Thus [muK] does not match the (eta-expanded) partial
application [mu1 (mk m)], and we provide a separate lemma for this. *)
lemma muK' (m : 'a -> real) : isdistr m => mu1 (mk m) = m. 
proof. by move=> dm; apply/fun_ext => x; apply muK. qed.

lemma mkK (d : 'a distr): mk (mu1 d) = d.
proof. 
by elim/distrW: d => m dm /=; congr; apply/fun_ext => x; rewrite muK.
qed.

lemma ge0_mu1 ['a] (d : 'a distr) (x : 'a) : 0%r <= mu1 d x.
proof. 
by elim/distrW: d => m dm; rewrite muK //; apply ge0_isdistr.
qed.

hint exact : ge0_mu1.

lemma le1_mu1_fin ['a] (d : 'a distr) (s : 'a list) :
  uniq s => big predT (mu1 d) s <= 1%r.
proof. by elim/distrW: d => m dm; rewrite muK' //; apply le1_sum_isdistr. qed.

lemma le1_mu1 ['a] (d : 'a distr) x : mu1 d x <= 1%r.
proof. by have := le1_mu1_fin d [x] _; rewrite ?big_seq1. qed.

hint exact : le1_mu1.

lemma isdistr_mu1 (d : 'a distr) : isdistr (mu1 d).
proof. by split; [exact/ge0_mu1 | exact/le1_mu1_fin]. qed.

lemma isdistr_comp ['a 'b] f (g : 'a -> 'b) :
  injective g => isdistr f => isdistr (f \o g).
proof.
move=> inj_g [ge0_f le1]; split; first by move=> x; apply: ge0_f.
move=> s uq_s; rewrite -(@big_map _ predT).
apply: le1; rewrite map_inj_in_uniq //.
by move=> x y _ _; apply: inj_g.
qed.

lemma ge0_mu (d : 'a distr) p : 0%r <= mu d p.
proof. by rewrite muE; apply/ge0_sum=> x /=; case: (p x). qed.

hint exact : ge0_mu.

lemma summable_mu1 ['a] (d : 'a distr) : summable (mu1 d).
proof.
exists 1%r=> s eq_s; rewrite (@eq_bigr _ _ (mu1 d)) => /=.
  by move=> i _; rewrite ger0_norm //.
by apply/le1_mu1_fin.
qed.

lemma summable_mu1_cond (d : 'a distr) (p : 'a -> bool) :
  summable (fun x => if p x then mu1 d x else 0%r).
proof. by apply/summable_cond/summable_mu1. qed.

(* TODO: assuming (forall x, |F x| <= k) would suffice *)
lemma summable_mu1_wght (d : 'a distr) (F : 'a -> real) :
     (forall x, 0%r <= F x <= 1%r)
  => summable (fun x => mu1 d x * F x).
proof. 
move=> dF; apply (summableM_bound 1%r); 1,3: smt().
by apply: summable_mu1.
qed.

lemma le1_mu (d : 'a distr) p : mu d p <= 1%r.
proof.
rewrite muE &(lerfin_sum) 1:&(summable_mu1_cond) => J uqJ.
apply: (@ler_trans (big predT (mu1 d) J)).
+ by apply: ler_sum => /= a _; case: (p a).
+ by apply: le1_mu1_fin.
qed.

hint exact : le1_mu.

lemma mu_bounded (d : 'a distr) (p : 'a -> bool) : 0%r <= mu d p <= 1%r.
proof. by rewrite ge0_mu le1_mu. qed.

lemma countable_mu1 ['a] (d : 'a distr):
  countable (fun x => mu1 d x <> 0%r).
proof. by apply/sbl_countable/summable_mu1. qed.

lemma eq_distr (d1 d2 : 'a distr):
  (d1 = d2) <=> (forall x, mu1 d1 x = mu1 d2 x).
proof.
split=> [->//|eq_mu]; rewrite -(@mkK d1) -(@mkK d2).
by congr; apply/fun_ext.
qed.

lemma isdistr_finP (s : 'a list) (m : 'a -> real) :
     uniq s
  => (forall x, m x <> 0%r => mem s x)
  => (forall x, 0%r <= m x)
  => (isdistr m <=> (big predT m s <= 1%r)).
proof.
move=> uq_s fin ge0_m; split=> [[_ /(_ s uq_s)]|le1_m] //.
split=> // s' uq_s'; rewrite (@bigID _ _ (mem s)) addrC big1 /=.
  by move=> i [_] @/predC; apply/contraR=> /fin.
rewrite -big_filter; apply/(ler_trans _ _ le1_m).
rewrite filter_predI filter_predT; pose t := filter _ _.
suff /eq_big_perm ->: perm_eq t (filter (mem s') s).
  rewrite big_filter (@bigID predT _ (mem s')) ler_addl.
  by rewrite sumr_ge0 => x _; apply/ge0_m.
apply/uniq_perm_eq; rewrite ?filter_uniq // => x.
by rewrite !mem_filter andbC.
qed.

(* -------------------------------------------------------------------- *)
abbrev weight (d:'a distr): real = mu d predT.

lemma ge0_weight ['a] (d : 'a distr) : 0%r <= weight d.
proof.
rewrite -sum0<:'a> muE; apply/RealSeries.ler_sum=> /=; first last.
+ by apply/summable0.
+ by rewrite -(@eq_summable (mu1 d)) ?summable_mu1.
+ by move=> x @/predT /=; apply/ge0_mu1.
qed.

lemma weightE (d : 'a distr) : weight d = sum (mu1 d).
proof. by rewrite muE; apply/eq_sum=> x /=. qed.

lemma weight_eq0 ['a] (d : 'a distr) :
  weight d = 0%r => (forall x, mu1 d x = 0%r).
proof. by rewrite weightE sump_eq0P //; exact summable_mu1. qed.

(* -------------------------------------------------------------------- *)
op support (d : 'a distr) x = 0%r < mu1 d x.

abbrev (\in) (x : 'a) (d : 'a distr) = support d x.
abbrev (\notin) (x : 'a) (d : 'a distr) = !support d x.

lemma supportP (d : 'a distr) x : (x \in d) <=> (mu1 d x <> 0%r).
proof. by rewrite eqr_le ge0_mu1 /= lerNgt. qed.

lemma supportPn (d : 'a distr) x : (x \notin d) <=> (mu1 d x = 0%r).
proof. by rewrite supportP eq_sym. qed.

pred is_lossless (d : 'a distr) = weight d = 1%r.

pred is_full (d : 'a distr) = forall x, x \in d.

lemma is_losslessP (d : 'a distr) : is_lossless d => weight d = 1%r.
proof. done. qed.

lemma is_fullP (d : 'a distr) x : is_full d => x \in d.
proof. by apply. qed.

pred is_uniform (d : 'a distr) = forall (x y : 'a),
  x \in d => y \in d => mu1 d x = mu1 d y.

pred is_funiform (d : 'a distr) = forall (x y : 'a), mu1 d x = mu1 d y.

lemma is_full_funiform (d : 'a distr) :
  is_full d => is_uniform d => is_funiform d.
proof. by move=> Hf Hu x y; apply: Hu; apply: Hf. qed.

lemma funi_uni (d : 'a distr) : is_funiform d => is_uniform d.
proof. by move=> h ????; apply: h. qed.

lemma funi_neq0_full (d : 'a distr) :
  is_funiform d => 0%r < weight d => is_full d.
proof.
move=> funi_d ll_d x; suff: exists y, y \in d.
+ by case=> y; rewrite !supportP (@funi_d x y).
move: ll_d; apply/contraLR; rewrite negb_exists /= => h.
rewrite (_ : weight d = 0%r) // muE.
rewrite sum0_eq //= => @/predT /= y.
by rewrite -supportPn h.
qed.

lemma funi_ll_full (d : 'a distr) :
  is_funiform d => is_lossless d => is_full d.
proof. by move=> funi_d ll_d; rewrite &(funi_neq0_full) // ll_d. qed.

lemma rnd_funi ['a] (d : 'a distr) :
  is_funiform d => forall x y, mu1 d x = mu1 d y.
proof. by apply. qed.

hint solve 1 random : rnd_funi is_losslessP is_fullP.

(* -------------------------------------------------------------------- *)
lemma mu_le (d : 'a distr) (p q : 'a -> bool):
     (forall x, x \in d => p x => q x)
  => mu d p <= mu d q.
proof. 
move=> le_pq; rewrite !muE ler_sum /=; 2,3: exact summable_mu1_cond.
move=> x; case: (p x) => Px; case: (q x) => Qx //=.
case: (x \in d); first by move/le_pq => /(_ Px).
by move/supportPn => ->. 
qed.

lemma mu_sub (d:'a distr) (p q:('a -> bool)):
  p <= q => mu d p <= mu d q.
proof. by move=> le_pq; apply/mu_le => ??; apply/le_pq. qed.

lemma mu_eq (d:'a distr) (p q:'a -> bool):
  p == q => mu d p = mu d q.
proof.
by move=> ext_p_q; congr=> //; apply fun_ext.
qed.

lemma eq0_mu ['a] d p : mu<:'a> d p = 0%r => forall x, x \in d => !p x.
proof.
move=> eq0 x xd; apply: contraL eq0 => px; rewrite gtr_eqF //.
apply: (@ltr_le_trans (mu1 d x)); last by apply: mu_le => y _ ->.
by move/supportP: xd; rewrite ltr_neqAle ge0_mu /= eq_sym.
qed.

lemma mu_eq_support : forall (d : 'a distr) (p q : 'a -> bool),
  (forall (x : 'a), x \in d => p x = q x) => mu d p = mu d q.
proof. smt (mu_le). qed.

lemma eq1_mu ['a] (d : 'a distr) p :
  is_lossless d => (forall x, x \in d => p x) => mu d p = 1%r.
proof.
move=> ll_d pT; rewrite (@mu_eq_support _ _ predT).
- by move=> x xd; rewrite pT.
- by apply: ll_d.
qed.

lemma mu0 (d : 'a distr) : mu d pred0 = 0%r.
proof. by rewrite muE /pred0 /= sum0. qed.

lemma mu0_false ['a] (d : 'a distr) (p : 'a -> bool) :
  (forall x, x \in d => !p x) => mu d p = 0%r.
proof. by rewrite -(@mu0 d)=> H;apply mu_eq_support => x /H ->. qed.

lemma neq0_mu ['a] (d : 'a distr) p :
  mu d p <> 0%r => exists x, x \in d /\ p x.
proof.
apply: contraR; rewrite negb_exists /= => z_d.
by apply: mu0_false => /#.
qed.

axiom mu_or (d : 'a distr) (p q : 'a -> bool):
  mu d (predU p q) = mu d p + mu d q - mu d (predI p q).

lemma mu_and (d : 'a distr) (p q : 'a -> bool) :
  mu d (predI p q) = mu d p + mu d q - mu d (predU p q).
proof. by rewrite (@mu_or d p q) #ring. qed.

lemma mu_disjoint (d : 'a distr) (p q : 'a -> bool):
  (predI p q) <= pred0 => mu d (predU p q) = mu d p + mu d q.
proof.
move=> h; rewrite mu_or (@mu0_false _ (predI _ _)) //.
by move=> x _; apply/negP => /h.
qed.

lemma mu_disjointL (d : 'a distr) (p q : 'a -> bool) :
  (forall x, p x => !q x) => mu d (predU p q) = mu d p + mu d q.
proof. by move=> h; rewrite mu_disjoint // => x [/h]. qed.

lemma mu_split (d : 'a distr) (p q : 'a -> bool) :
  mu d p = mu d (predI p q) + mu d (predI p (predC q)).
proof.
have {1}->: p = predU (predI p q) (predI p (predC q)).
+ by apply/fun_ext=> x /#.
+ by rewrite mu_disjointL 1:/#.
qed.

lemma mu_not (d : 'a distr) (p : 'a -> bool):
  mu d (predC p) = weight d - mu d p.
proof. by rewrite -(@predCU p) mu_disjointL // #ring. qed.

lemma witness_support P (d : 'a distr) :
  0%r < mu d P <=> (exists x, P x /\ x \in d).
proof.
have ->: 0%r < mu d P <=> mu d P <> 0%r by smt(ge0_mu).
split=> />.
+ apply: contraLR=> /= /negb_exists /> empty.
  apply: mu0_false=> x x_in_D; move: (empty x).
  by case: (P x).
move=> x Px x_in_D; rewrite -negP=> /eq0_mu /=.
by rewrite negb_forall; exists x=> /=; rewrite x_in_D Px.
qed.

lemma mu_and_weight ['a] P Q (d : 'a distr) : (* FIXME: name *)
  mu d P = weight d => mu d (predI P Q) = mu d Q.
proof.
move=> h; rewrite mu_and; suff ->: mu d (predU P Q) = mu d P by smt().
by rewrite eqr_le {1}h !mu_le // => x _ Px; left.
qed.

lemma mu_in_weight ['a] P (d : 'a distr) x :
  mu d P = weight d => x \in d => P x.
proof.
move/(mu_and_weight _ (pred1 x)) => @/support <-.
by case/witness_support=> y /> Py <-.
qed.

lemma weightE_support ['a] (d : 'a distr) : weight d = mu d (support d).
proof.
rewrite (@mu_split _ _ (support d)); pose p := predI _ (predC _).
have ->: predI predT (support d) = support d by apply/fun_ext.
suff ->: mu d p = 0%r by rewrite addr0. by rewrite mu0_false.
qed.

lemma mu_le_weight ['a] (d : 'a distr) p : mu d p <= weight d.
proof. by apply/mu_le. qed.

lemma mu_le_eq ['a] (d1 d2 : 'a distr) :
  is_lossless d1 =>
  (forall p, mu d1 p <= mu d2 p) =>
  d1 = d2.
proof.
rewrite eq_distr => d1_ll d1_leq_d2 x.
case (mu1 d1 x = mu1 d2 x) => // *.
suff: (weight d1 < weight d2) by smt(mu_bounded).
have weight_decomp : forall d,
  weight d = mu1 d x + mu d (predC (pred1 x)) by smt(mu_not).
do 2 ! rewrite weight_decomp.
by apply ltr_le_add => /#.
qed.

lemma mu1_le_eq ['a] (d1 d2 : 'a distr) :
  is_lossless d1 =>
  (forall x, mu1 d1 x <= mu1 d2 x) =>
  d1 = d2.
proof.
move => d1_ll d1_leq_d2.
apply mu_le_eq => // p.
rewrite muE muE.
apply RealSeries.ler_sum; 2,3: exact summable_mu1_cond.
move => x. case: (p x) => /> *.
exact d1_leq_d2.
qed.

lemma mu1_le_eq_mu1 ['a] (d1 d2 : 'a distr) :
  is_lossless d1 =>
  (forall x, mu1 d1 x <= mu1 d2 x) =>
  forall x, mu1 d1 x = mu1 d2 x.
proof.
move => d1_ll d1_le_d2.
by rewrite (mu1_le_eq d1_ll d1_le_d2).
qed.

(* -------------------------------------------------------------------- *)

lemma mu_has_le ['a 'b] (P : 'a -> 'b -> bool) (d : 'a distr) (s : 'b list) :
   mu d (fun a => has (P a) s) <= BRA.big predT (fun b => mu d (fun a => P a b)) s.
proof.
elim: s => [|x s ih]; first by rewrite big_nil mu0.
rewrite big_cons {1}/predT /= mu_or.
apply (ler_trans (mu d (transpose P x) + mu d (fun (x0 : 'a) => has (P x0) s))).
+ smt(mu_bounded).
by rewrite ler_add2l.
qed.

lemma mu_has_leM ['a 'b] (P : 'a -> 'b -> bool) (d : 'a distr) (s : 'b list) r :
  (forall b, b \in s => mu d (fun a => P a b) <= r) =>
  mu d (fun a => has (P a) s) <= (size s)%r * r.
proof.
move=> le; apply/(ler_trans (big predT (fun x => r) s)).
+ by have /ler_trans := mu_has_le P d s; apply; apply/ler_sum_seq => ? /le.
by rewrite Bigreal.sumr_const count_predT.
qed.

(* -------------------------------------------------------------------- *)
lemma mu_mem_uniq ['a] (d : 'a distr) (s : 'a list) :
  uniq s => mu d (mem s) = BRA.big predT (mu1 d) s.
proof.
elim: s => [_|x s ih [xs uq_s]]; first by rewrite big_nil mu0.
rewrite big_cons {1}/predT /= -ih // -mu_disjointL => [y ->//|].
by apply/mu_eq=> y.
qed.

lemma mu_mem ['a] (d : 'a distr) (s : 'a list) :
  mu d (mem s) = BRA.big predT (mu1 d) (undup s).
proof.
rewrite -mu_mem_uniq ?undup_uniq; apply/mu_eq.
by move=> x; rewrite mem_undup.
qed.

lemma mu_mem_le ['a] (d : 'a distr) (s : 'a list) :
  mu d (mem s) <= BRA.big predT (mu1 d) s.
proof.
rewrite sumr_undup mu_mem; apply/ler_sum_seq => //= x.
rewrite mem_undup => x_in_s _; rewrite intmulr.
apply/ler_pemulr; first by apply/ge0_mu.
by rewrite le_fromint -(@ltzE 0) -has_count has_pred1.
qed.

lemma mu_mem_le_mu1 ['a] (d : 'a distr) (s : 'a list) r :
  (forall x, mu1 d x <= r) => mu d (mem s) <= (size s)%r * r.
proof.
move=> le; apply/(ler_trans (big predT (fun (x : 'a) => r) s)).
+ by have := mu_mem_le d s => /ler_trans; apply; apply/ler_sum.
by rewrite Bigreal.sumr_const count_predT.
qed.

lemma fin_muE (d : 'a distr) (E : 'a -> bool) : is_finite (support d) =>
  mu d E = big E (mu1 d) (to_seq (support d)).
proof.
move => fin_d.
rewrite (@mu_eq_support d _ (mem (filter E (to_seq (support d))))).
- by move => x x_d; rewrite mem_filter mem_to_seq // x_d.
by rewrite mu_mem_uniq ?filter_uniq ?uniq_to_seq // big_filter.
qed.

(* -------------------------------------------------------------------- *)

lemma mu_pos_fin (d : 'a distr) eps :
  0%r < eps => is_finite (fun x => eps <= mu1 d x).
proof.
move => eps_gt0; pose E x := eps <= mu1 d x.
suff: !is_finite E => 1%r < mu d E by smt(mu_bounded).
move => nFE; have := NfiniteP (ceil (inv eps) + 1) E _ nFE; 1: smt(ceil_ge).
case => L /> size_L L_uniq sub_L_E.
apply (ltr_le_trans (mu d (mem L))); last by apply mu_le => /#.
rewrite mu_mem_uniq //.
apply (ltr_le_trans (big predT (fun (x : 'a) => eps) L));
  last by apply ler_sum_seq.
rewrite sumr_const count_predT intmulr.
apply (ltr_le_trans (eps * (ceil (inv eps) + 1)%r)); last smt().
apply (ltr_le_trans (eps * ((inv eps) + 1%r))); first smt().
by rewrite ler_pmul2l //; smt(ceil_ge).
qed.

lemma uniform_finite ['a] (d : 'a distr) :
  is_uniform d => is_finite (support d).
proof.
case (exists x, x \in d) => [[x x_d] d_uni|]; last smt(finite0).
have -> : support d = (fun y => mu1 d x <= mu1 d y) by smt().
exact mu_pos_fin.
qed.

lemma mu1_uni ['a] (d : 'a distr) x : is_uniform d => mu1 d x =
  if x \in d then weight d / (size (to_seq (support d)))%r else 0%r.
proof.
move=> uf_d; case: (x \in d) => [xd|]; last first.
  by rewrite eqr_le ge0_mu /= lerNgt.
have fin_d := uniform_finite d uf_d.
rewrite weightE_support; have {1}->: support d = mem (to_seq (support d)).
  by apply/fun_ext=> y; rewrite mem_to_seq.
rewrite mu_mem_uniq ?uniq_to_seq //=; pose F := fun y => mu1 d y.
rewrite big_seq -(@eq_bigr _ (fun _ => mu1 d x)) /=.
  by move=> /= y; rewrite mem_to_seq // => yd; apply/uf_d.
rewrite -(@big_seq _ (to_seq (support d))).
rewrite Bigreal.sumr_const count_predT.
rewrite mulrAC divff // eq_fromint eq_sym eqr_le size_ge0 /=.
by rewrite lezNgt /= -has_predT hasP; exists x; rewrite mem_to_seq.
qed.

lemma mu1_uni_ll ['a] (d : 'a distr) x :
  is_uniform d => is_lossless d => mu1 d x =
    if x \in d then 1%r / (size (to_seq (support d)))%r else 0%r.
proof. by move=> uf_d ll_d; rewrite mu1_uni // ll_d. qed.

lemma eq_funi ['a] (d1 d2 : 'a distr) :
  is_funiform d1 => is_funiform d2 => weight d1 = weight d2 => d1 = d2.
proof.
move=> ^funi1 /funi_uni uni1 ^funi2 /funi_uni uni2 eq_wgt.
apply/eq_distr=> x; rewrite !mu1_uni // eq_wgt.
move: (ge0_weight d2) => /ler_eqVlt [<-//|^].
rewrite -{1}eq_wgt => gt0_w1 gt0_w2.
rewrite !funi_neq0_full //=; do 3! congr.
apply/perm_eq_size/uniq_perm_eq;
  1,2: by apply/uniq_to_seq/uniform_finite.
move=> a; rewrite !mem_to_seq ?uniform_finite //.
by rewrite !funi_neq0_full.
qed.

lemma eq_funi_ll ['a] (d1 d2 : 'a distr) :
     is_funiform d1 => is_lossless d1
  => is_funiform d2 => is_lossless d2
  => d1 = d2.
proof.
by move=> funi1 ll1 funi2 ll2; apply: eq_funi => //; rewrite ll1 ll2.
qed.

(* -------------------------------------------------------------------- *)

(* probability of the most likely output *)
op p_max (p: 'a distr) = flub (mu1 p).

lemma has_fub_mu1 (d: 'a distr) : has_fub (mu1 d).
proof. by apply: (@ler_has_fub _ (fun _=> 1%r))=> //; exists 1%r. qed.

lemma pmax_ge0 (p: 'a distr) :
  0%r <= p_max p.
proof.
suff: mu1 p witness <= p_max p by smt(ge0_mu).
by apply: (@flub_upper_bound (mu1 p)); exists 1%r; smt(le1_mu).
qed.

lemma pmax_gt0 (p: 'a distr) x :
  x \in p => 0%r < p_max p.
proof.
move => in_xp; suff: p_max p >= mu1 p x by smt(ge0_mu).
apply: (@flub_upper_bound (mu1 p)); exists 1%r; smt(le1_mu).
qed.

lemma pmax_le1 (p: 'a distr) :
  p_max p <= 1%r.
proof. by rewrite flub_le_ub. qed.

lemma pmax_upper_bound (d: 'a distr) (x: 'a) :
  mu1 d x <= p_max d.
proof.
apply (@flub_upper_bound (mu1 d) x); exists 1%r => /=.
by move => ?; apply le1_mu.
qed.

lemma uniform_pmaxE (d: 'a distr) :
  is_uniform d =>
  p_max d = weight d / (size (to_seq (support d)))%r.
proof.
move => unif_d; apply eqr_le; split.
- apply flub_le_ub => /= x.
  rewrite mu1_uni //.
  case (x \in d) => _; first by trivial.
  apply divr_ge0; first exact ge0_weight.
  smt(size_ge0).
- move => _; case (weight d = 0%r) => ?; first by smt(pmax_ge0).
  have [x in_xd]: exists x, x \in d.
  + move: (witness_support predT d)=> /iffLR /(_ _); 1:smt(ge0_mu).
    by rewrite /predT.
  have <-: mu1 d x = weight d / (size (to_seq (support d)))%r by smt(mu1_uni).
  by apply: (@flub_upper_bound (mu1 d)) => /=; exists 1%r; smt(le1_mu).
qed.

(* -------------------------------------------------------------------- *)

op mnull ['a] = fun (x : 'a) => 0%r.
op dnull ['a] = mk mnull<:'a>.

lemma isdistr_mnull ['a] : isdistr mnull<:'a>.
proof. by split=> //= s _; rewrite Bigreal.sumr_const mulr0. qed.

lemma dnull1E ['a] : forall x, mu1 dnull<:'a> x = 0%r.
proof. by move=> x; rewrite muK //; apply/isdistr_mnull. qed.

lemma dnullE ['a] (E : 'a -> bool) : mu dnull<:'a> E = 0%r.
proof.
rewrite muE -(@eq_sum (fun x=> 0%r)) 2:sum0 //.
by move=> x /=; rewrite dnull1E if_same.
qed.

lemma weight_dnull ['a] : weight dnull<:'a> = 0%r.
proof. by apply/dnullE. qed.

lemma supp_dnull (x:'a) : x \notin dnull.
proof. by rewrite /support dnull1E. qed.

lemma dnull_uni ['a]: is_uniform dnull<:'a>.
proof. by move=> x y;rewrite !dnull1E. qed.

lemma dnull_fu ['a]: is_funiform dnull<:'a>.
proof. by move=> x y;rewrite !dnull1E. qed.

lemma support_eq0 ['a] (d : 'a distr) : (forall x, x \notin d) => d = dnull.
proof.
rewrite (@forall_iff _ (fun x=> mu1 d x = 0%r)) /=.
+ move=> x /=; rewrite /support -lerNgt.
  by split=> [le0_dx|->] //; apply/ler_asym; rewrite le0_dx ge0_mu1.
by move=> h; apply/eq_distr=> x; rewrite h dnull1E.
qed.

lemma weight_eq0_dnull ['a] (d : 'a distr) : weight d = 0%r => d = dnull.
proof.
by move=> /weight_eq0 dx_eq0; apply/eq_distr=> x; rewrite dnull1E dx_eq0.
qed.

lemma distr_0Vmem (d : 'a distr) : d = dnull \/ exists x, x \in d.
proof.
have := pred_0Vmem (support d); smt(support_eq0 supportP).
qed.

lemma pmax_dnull ['a] : p_max dnull<:'a> = 0%r.
proof.
rewrite /p_max.
have ->: (mu1 dnull<:'a>) = fun _ => 0%r by smt(dnull1E).
exact flub_const.
qed.



(* -------------------------------------------------------------------- *)
theory MRat.

pred eq_ratl (s1 s2 : 'a list) =
  (s1 = [] <=> s2 = []) /\
  perm_eq
    (flatten (nseq (size s2) s1))
    (flatten (nseq (size s1) s2)).

lemma perm_eq_ratl (s1 s2 : 'a list):
  perm_eq s1 s2 => eq_ratl s1 s2.
proof.
move=> ^eq_s12 /perm_eqP eqp_s12; split.
  by split=> ->>; apply/perm_eq_small=> //; apply/perm_eq_sym.
apply/perm_eqP=> p; rewrite !count_flatten_nseq.
by rewrite eqp_s12 (perm_eq_size eq_s12).
qed.

lemma ratl_mem (s1 s2 : 'a list) :
  eq_ratl s1 s2 => forall x, mem s1 x <=> mem s2 x.
proof.
case=> eqvnil /perm_eq_mem h x; move/(_ x): h.
rewrite -!has_pred1 !has_count !count_flatten_nseq.
rewrite !ler_maxr ?size_ge0; case: (s1 = []) => [^/eqvnil -> ->//|nz_s1].
rewrite !IntOrder.pmulr_rgt0 ?lt0n ?size_ge0 ?size_eq0 -?eqvnil //.
by rewrite count_ge0. by rewrite count_ge0.
qed.

op mrat ['a] (s : 'a list) =
  fun x => (count (pred1 x) s)%r / (size s)%r.

lemma isdistr_drat (s : 'a list) : isdistr (mrat s).
proof.
rewrite /mrat; split=> /= [x|J uq_J].
  by rewrite divr_ge0 // le_fromint ?(count_ge0, size_ge0).
rewrite -divr_suml -sumr_ofint; have := size_ge0 s.
rewrite IntOrder.ler_eqVlt => -[<-//|nz_s].
rewrite ler_pdivr_mulr 1?lt_fromint // mul1r le_fromint.
rewrite -{2}(@filter_predT s) -big_count.
have /BIA.eq_big_perm <- := perm_filterC (mem s) J.
rewrite BIA.big_cat IntID.addrC BIA.big_seq BIA.big1 /=.
+ move=> i; rewrite mem_filter => -[@/predC i_notin_s _].
  by rewrite -count_eq0 has_pred1.
have /BIA.eq_big_perm <- := perm_filterC (mem J) (undup s).
rewrite BIA.big_cat ler_paddr ?sumr_ge0 /=.
+ by move=> x _; rewrite count_ge0.
rewrite lerr_eq &(BIA.eq_big_perm) uniq_perm_eq //.
+ by rewrite filter_uniq.
+ by rewrite filter_uniq undup_uniq.
by move=> x; rewrite !mem_filter mem_undup andbC.
qed.

op drat ['a] (s : 'a list) = mk (mrat s).

lemma dratE ['a] (s : 'a list) (x : 'a):
  mu1 (drat s) x = (count (pred1 x) s)%r / (size s)%r.
proof. by rewrite muK // isdistr_drat. qed.

lemma prratE ['a] (s : 'a list) (E : 'a -> bool) :
  mu (drat s) E = (count E s)%r / (size s)%r.
proof.
rewrite muE (@sumE_fin _ (undup s)) ?undup_uniq //=.
  move=> x; case: (E x)=> _ //; rewrite dratE.
  rewrite mulf_eq0 negb_or mem_undup eq_fromint => -[+ _].
  by rewrite -lt0n ?count_ge0 // -has_count has_pred1.
pose F := fun x => (count (pred1 x) s)%r / (size s)%r.
rewrite -big_mkcond (@eq_bigr _ _ F) /F /= => {F}.
  by move=> i _; rewrite dratE.
by rewrite -size_filter -divr_suml -sumr_ofint big_count.
qed.

lemma supp_drat (s : 'a list) x : x \in (drat s) <=> x \in s.
proof.
rewrite /support dratE -has_pred1 has_count.
case: (count (pred1 x) s <= 0); [smt(count_ge0)|].
move=> /IntOrder.ltrNge ^ + -> /=; rewrite -lt_fromint; case: s=> //=.
move=> ? s /(@mulr_gt0 _ (inv (1 + size s)%r)) -> //.
by rewrite invr_gt0 lt_fromint #smt:(size_ge0).
qed.

lemma eq_dratP ['a] (s1 s2 : 'a list) :
  eq_ratl s1 s2 <=> (drat s1 = drat s2).
proof.
split=> [[]|eq_d].
  move=> eqvnil eq_s12; apply/eq_distr=> x; rewrite !dratE.
  move/perm_eqP/(_ (pred1 x)): eq_s12; rewrite !count_flatten_nseq.
  rewrite !ler_maxr ?size_ge0; case: (s1 = []).
    by move=> ^/eqvnil -> ->.
  move=> ^nz_s1; rewrite eqvnil => nz_s2.
  rewrite eqf_div ?eq_fromint ?size_eq0 // -!fromintM.
  by rewrite eq_fromint !(@mulzC (size _)).
apply/andaE; split.
  have h: forall t1 t2, drat<:'a> t1 = drat t2 => t1 = [] => t2 = [].
    move=> t1 [|x t2] eq_dt ->>//; move/(congr1 (fun d => mu1 d x)): eq_dt.
    rewrite /= !dratE /= eq_sym mulf_neq0 // ?invr_eq0 eq_fromint.
    by apply/add1z_neq0/count_ge0. by apply/add1z_neq0/size_ge0.
  by split=> z_s; [apply/(h s1)|apply/(h s2)]=> //; apply/eq_sym.
case: s1 s2 eq_d => [|x1 s1] [|x2 s2] //=.
  by apply/perm_eq_refl.
move=> eq_d; apply/perm_eqP=> p; rewrite !count_flatten_nseq.
move/(congr1 (fun d => mu d p)): eq_d => /=; rewrite !prratE /=.
rewrite !ler_maxr ?addr_ge0 ?size_ge0 // eqf_div;
  try by rewrite eq_fromint add1z_neq0 ?size_ge0.
by rewrite -!fromintM eq_fromint !(@mulzC (1 + _)).
qed.

lemma perm_eq_drat ['a] (s1 s2 : 'a list) :
  perm_eq s1 s2 => drat s1 = drat s2.
proof. by move => ?; apply/eq_dratP/perm_eq_ratl. qed.

lemma eq_sz_dratP ['a] (s1 s2 : 'a list) : size s1 = size s2 =>
  perm_eq s1 s2 <=> (drat s1 = drat s2).
proof.
move=> eq_sz; rewrite -eq_dratP /eq_ratl -!size_eq0 -!eq_sz /=.
split=> /perm_eqP eq; apply/perm_eqP=> p; rewrite ?count_flatten_nseq ?eq //.
move/(_ p): eq; rewrite !count_flatten_nseq ler_maxr ?size_ge0.
case: (s1 = []) => [->>|] /=.
  suff ->//: s2 = []; by rewrite -size_eq0 -eq_sz.
by rewrite -size_eq0 => nz_s1 /(IntID.mulfI _ nz_s1).
qed.

lemma drat_ll ['a] (s : 'a list) :
  s <> [] => mu (drat s) predT = 1%r.
proof.
move=> nz_s; rewrite prratE count_predT divrr //.
by rewrite eq_fromint size_eq0.
qed.
end MRat.

(* --------------------------------------------------------------------- *)
theory MUnit.

op dunit ['a] (x : 'a) = MRat.drat [x].

lemma dunit1E ['a] (x y : 'a):
  mu1 (dunit x) y = b2r (x = y).
proof. by rewrite MRat.dratE /= /pred1; case: (x = y). qed.

lemma dunit1xx ['a] (x : 'a): mu1 (dunit x) x = 1%r.
proof. by rewrite dunit1E. qed.

lemma dunitE ['a] (E : 'a -> bool) (x : 'a):
  mu (dunit x) E = b2r (E x).
proof. by rewrite MRat.prratE /=; case: (E x). qed.

lemma dunit_ll ['a] (x : 'a): mu (dunit x) predT = 1%r.
proof. by apply/MRat.drat_ll. qed.

lemma supp_dunit ['a] (x x': 'a): x' \in (dunit x) <=> (x' = x).
proof. by rewrite MRat.supp_drat. qed.

lemma dunit_uni ['a] (x : 'a) : is_uniform (dunit x).
proof. by move=> x1 x2;rewrite !supp_dunit => -> ->. qed.

lemma finite_dunit ['a] (x : 'a) : is_finite (support (dunit x)).
proof. by apply/uniform_finite/dunit_uni. qed.

lemma pmax_dunit (x: 'a) :
  p_max (dunit x) = 1%r.
proof.
rewrite eqr_le pmax_le1 /=.
apply: ler_trans (pmax_upper_bound (dunit x) x).
by rewrite dunit1E.
qed.

end MUnit.
export MUnit.

(* -------------------------------------------------------------------- *)
theory MUniform.

op duniform ['a] (s : 'a list) = MRat.drat (undup s).

lemma duniform1E ['a] (s : 'a list) x :
  mu1 (duniform s) x = if mem s x then 1%r / (size (undup s))%r else 0%r.
proof.
rewrite MRat.dratE count_uniq_mem ?undup_uniq // mem_undup.
by case: (mem s x)=> //= @/b2i.
qed.

lemma duniform1E_uniq ['a] (s : 'a list) x : uniq s =>
  mu1 (duniform s) x = if x \in s then 1%r / (size s)%r else 0%r.
proof.
move=> uq_s; rewrite duniform1E.
by case: (x \in s) => // _; rewrite undup_id //.
qed.

lemma eq_duniformP ['a] (s1 s2 : 'a list) :
     (forall x, mem s1 x <=> mem s2 x)
 <=> (duniform s1 = duniform s2).
proof.
rewrite -MRat.eq_dratP; split=> h.
  apply/MRat.perm_eq_ratl/uniq_perm_eq; rewrite ?undup_uniq=> //.
  by move=> x; rewrite !mem_undup; apply/h.
move=> x; rewrite -(@mem_undup s1) -(@mem_undup s2).
by apply/MRat.ratl_mem.
qed.

lemma duniformE ['a] (E : 'a -> bool) (s : 'a list) :
  mu (duniform s) E = (count E (undup s))%r / (size (undup s))%r.
proof. by apply/MRat.prratE. qed.

lemma supp_duniform ['a] (s : 'a list) x: x \in (duniform s) <=> x \in s.
proof. by rewrite MRat.supp_drat; rewrite mem_undup. qed.

lemma duniform_ll (s : 'a list) :
  s <> [] => is_lossless (duniform s).
proof. by move=> nz_s; apply/MRat.drat_ll; rewrite undup_nilp. qed.

lemma duniform_uni (s : 'a list) : is_uniform (duniform s).
proof. by move=> x y; rewrite !duniform1E !supp_duniform => !->. qed.

lemma duniform_fu (s: 'a list) :
  (forall x, x \in s) =>
  is_full (duniform s).
proof. by move=> hin x; rewrite supp_duniform hin. qed.

lemma finite_duniform ['a] (s : 'a list) : is_finite (support (duniform s)).
proof. by apply/uniform_finite/duniform_uni. qed.
end MUniform.
export MUniform.

(* -------------------------------------------------------------------- *)
abstract theory MFinite.
type t.

clone import FinType as Support with type t <- t.

op dunifin : t distr = MUniform.duniform enum.

lemma dunifin1E (x : t) : mu1 dunifin x = 1%r / card%r.
proof. by rewrite MUniform.duniform1E enumP /= undup_id // enum_uniq. qed.

lemma dunifinE (E : t -> bool) :
  mu dunifin E = (count E enum)%r / card%r.
proof. by rewrite MUniform.duniformE ?undup_id // enum_uniq. qed.

lemma supp_dunifin x: x \in dunifin.
proof.
by rewrite MUniform.supp_duniform Support.enumP.
qed.

lemma dunifin_ll : is_lossless dunifin.
proof.
rewrite MUniform.duniform_ll -size_eq0 -lt0n.
  by rewrite size_ge0. by rewrite Support.card_gt0.
qed.

lemma dunifin_uni : is_uniform dunifin.
proof. apply MUniform.duniform_uni. qed.

lemma dunifin_fu : is_full dunifin.
proof. by move=> x;rewrite supp_dunifin. qed.

lemma dunifin_funi : is_funiform dunifin.
proof.
by apply is_full_funiform;[apply dunifin_fu|apply dunifin_uni].
qed.

hint exact random : dunifin_ll dunifin_fu dunifin_funi.

end MFinite.

(* -------------------------------------------------------------------- *)
theory MIntUniform.
op drange (m n : int) = MUniform.duniform (range m n).

lemma drange1E (m n x : int):
  mu1 (drange m n) x = if m <= x < n then 1%r / (n - m)%r else 0%r.
proof.
rewrite MUniform.duniform1E mem_range undup_id 1:range_uniq //.
rewrite size_range; case: (m <= x < n) => // -[le_mx lt_xn].
rewrite ler_maxr // IntOrder.subr_ge0 IntOrder.ltrW //.
by apply (IntOrder.ler_lt_trans _ le_mx).
qed.

lemma drangeE (E : int -> bool) (m n : int) :
  mu (drange m n) E = (count E (range m n))%r / (n - m)%r.
proof.
rewrite MUniform.duniformE undup_id 1:range_uniq //.
rewrite size_range; case: (lezWP n m) => [le_nm|le_mn].
  by rewrite ler_maxl // 1:subr_le0 // range_geq //.
by rewrite ler_maxr // subr_ge0 ltrW // ltzNge.
qed.

lemma supp_drange (m n i : int): i \in drange m n <=> m <= i < n.
proof. by rewrite MRat.supp_drat undup_id ?range_uniq mem_range. qed.

lemma drange_ll (m n : int) : m < n => is_lossless (drange m n).
proof. by move=> H;apply MUniform.duniform_ll;rewrite range_ltn. qed.

lemma drange_uni (m n : int) : is_uniform (drange m n).
proof. apply MUniform.duniform_uni. qed.
end MIntUniform.

export MIntUniform.


(* -------------------------------------------------------------------- *)

(* Even though p_max is defined as a lub, the maximum is always attained*)
lemma pmaxE (d : 'a distr) : exists x, p_max d = mu1 d x.
proof.
have [->|[x x_d]] := distr_0Vmem d.
- by exists witness; rewrite pmax_dnull dnullE.
have [L memL] := mu_pos_fin d (mu1 d x) _; 1: smt(ge0_mu).
have [y /= [y_L y_max]] := maxr_seq (mu1 d) L x _; 1: smt().
exists y; rewrite eqr_le pmax_upper_bound /=.
by apply flub_le_ub => z /#.
qed.

(* one of the elements with the highest probability *)
op mode (d: 'a distr) = choiceb (fun x => p_max d = mu1 d x) witness.

lemma mode_ge (d: 'a distr) x: mu1 d x <= mu1 d (mode d). 
proof. 
  suff <-: p_max d = mu1 d (mode d) by apply pmax_upper_bound.
  have /choicebP /= /#: exists x, p_max d = mu1 d x by apply pmaxE.
qed.

(* -------------------------------------------------------------------- *)
op mlet ['a 'b] (d : 'a distr) (f : 'a -> 'b distr) =
  fun (y : 'b) => sum<:'a> (fun x => mu1 d x * mu1 (f x) y).

op dlet ['a 'b] (d : 'a distr) (f : 'a -> 'b distr) =
  mk (mlet d f).

lemma isdistr_mlet ['a 'b] (d : 'a distr) (f : 'a -> 'b distr) :
  isdistr (mlet d f).
proof.
split=> [x|]; first by apply/ge0_sum=> y /=; rewrite mulr_ge0.
move=> J uqJ @/mlet; rewrite -sum_big /=.
+ by move=> y _; apply: summable_mu1_wght.
apply: (@ler_trans (sum (mu1 d))); last by rewrite -weightE.
apply: RealSeries.ler_sum => /=.
+ by move=> x; rewrite -mulr_sumr ler_pimulr // (@le1_mu1_fin (f x)).
+ by apply: summable_big => y _ /=; apply: summable_mu1_wght.
+ by apply: summable_mu1.
qed.

lemma dlet1E (d : 'a distr) (f : 'a -> 'b distr) (b : 'b):
  mu1 (dlet d f) b = sum<:'a> (fun a => mu1 d a * mu1 (f a) b).
proof. by rewrite muK 1:isdistr_mlet. qed.

lemma dlet_muE (d : 'a distr) (f : 'a -> 'b distr) (P : 'b -> bool):
  mu (dlet d f) P
  = sum<:'b> (fun b =>
      sum<:'a> (fun a =>
        if P b then mu1 d a * mu1 (f a) b else 0%r)).
proof.
rewrite muE &(eq_sum) => y /=; rewrite dlet1E; case: (P y) => //.
by rewrite sum0.
qed.

lemma summable_dlet ['a 'b] d f:
  summable (fun (ab : 'a * 'b) => mu1 d ab.`1 * mu1 (f ab.`1) ab.`2).
proof.
pose G a b := mu1 (f a) b; apply/(@summableM_prod_dep (mu1 d) G).
  by apply/summable_mu1.
exists 1%r => a @/G @/(\o) J uqJ; rewrite (@eq_bigr _ _ (mu1 (f a))).
  by move=> b _ /=; rewrite ger0_norm.
by apply: le1_mu1_fin.
qed.

lemma dlet_muE_swap (d : 'a distr) (f : 'a -> 'b distr) (P : 'b -> bool):
  mu (dlet d f) P
  = sum<:'a> (fun a =>
      sum<:'b> (fun b =>
        if P b then mu1 d a * mu1 (f a) b else 0%r)).
proof.
pose F (ab : 'a * 'b) :=
  if P ab.`2 then mu1 d ab.`1 * mu1 (f ab.`1) ab.`2 else 0%r.
rewrite dlet_muE (@sum_swap F) // /F summable_cond summable_dlet.
qed.

lemma dletE (d : 'a distr) (F : 'a -> 'b distr) (E : 'b -> bool) : 
  mu (dlet d F) E = sum (fun x => mu1 d x * mu (F x) E).
proof. 
rewrite dlet_muE_swap; apply eq_sum => a /=. 
rewrite (@eq_sum _ (fun b => mu1 d a * if  E b then mu1 (F a) b else 0%r)).
  by move => x /=; case: (E x).
by rewrite sumZ -muE.
qed.

lemma dletE_bool ['u] (d : bool distr) (F : bool -> 'u distr) E :
  mu (dlet d F) E = mu1 d true * mu (F true) E + mu1 d false * mu (F false) E.
proof. by rewrite dletE (@sumE_fin _ [true; false]) //=; case. qed.

lemma const_weight_dlet r (d : 'a distr) (F : 'a -> 'b distr) : 
  (forall x, weight (F x) = r) => weight (dlet d F) = r * weight d.
proof.
move => wF; rewrite !dletE (@eq_sum _ (fun x => r * mu1 d x)) => [x /=|].
  by rewrite wF mulrC. 
by rewrite sumZ -weightE.
qed.

lemma weight_dlet (d:'a distr) (F:'a -> 'b distr) :
  weight (dlet d F) <= weight d.
proof.
rewrite dletE weightE; apply RealSeries.ler_sum; first last.
+ apply summable_mu1_wght; smt(mu_bounded).
+ exact summable_mu1.
by move => x /=; rewrite ler_pimulr ?ge0_mu ?le1_mu.
qed.

lemma supp_dlet (d : 'a distr) (F : 'a -> 'b distr) (b : 'b) :
  b \in (dlet d F) <=> exists a, a \in d /\ b \in (F a).
proof.
rewrite supportP dlet1E sump_eq0P /=.
+ by move=> x; rewrite mulr_ge0.
+ apply/(@summable_le (mu1 d)); first by apply/summable_mu1.
  by move=> x /=; rewrite normrM ler_pimulr ?normr_ge0 ger0_norm.
rewrite negb_forall /=; apply/exists_iff=> /= x.
by rewrite !supportP mulf_eq0 negb_or.
qed.

lemma dlet_d_unit (d:'a distr) : dlet d MUnit.dunit = d.
proof.
apply/eq_distr=> x; rewrite dlet1E /= (@sumE_fin _ [x]) //=.
+ by move=> x0; rewrite MUnit.dunit1E /=; case (x0 = x).
+ by rewrite big_consT big_nil /= MUnit.dunit1E.
qed.

lemma dlet_unit (F:'a -> 'b distr) a : dlet (MUnit.dunit a) F = F a.
proof.
apply/eq_distr=> x; rewrite dlet1E /= (@sumE_fin _ [a]) //=.
+ by move=> a0; rewrite MUnit.dunit1E (@eq_sym a); case (a0 = a).
+ by rewrite big_consT big_nil /= MUnit.dunit1E.
qed.

lemma dlet_dlet (d1:'a distr) (F1:'a -> 'b distr) (F2: 'b -> 'c distr):
  dlet (dlet d1 F1) F2 = dlet d1 (fun x1 => dlet (F1 x1) F2).
proof.
apply: eq_distr => c; rewrite !dlet1E.
pose F a b := mu1 d1 a * mu1 (F1 a) b * mu1 (F2 b) c.
rewrite (@eq_sum _ (fun y => sum (fun x => F x y))) => [y /=|].
  by rewrite dlet1E sumZr //. 
rewrite (@eq_sum _ (fun x => sum (fun y => F x y))) => [x /=|].
  by rewrite dlet1E -sumZ /= &(eq_sum) => y /=; rewrite mulrA.
suff smF: summable (fun ab : _ * _ => F ab.`1 ab.`2) by rewrite (sum_swap smF).
apply (@summableM_bound 1%r) => //= [|[x y] /=]; 1: exact summable_dlet. 
by rewrite ger0_norm ?ge0_mu le1_mu.
qed.

lemma dlet_dnull (F:'a -> 'b distr): dlet dnull F = dnull.
proof.
apply/eq_distr=> x; rewrite dlet1E dnull1E (@sumE_fin _ []) //= => x0.
by rewrite dnull1E.
qed.

lemma dlet_d_dnull (d : 'a distr): dlet d (fun a => dnull<:'b>) = dnull.
proof. by apply/eq_distr=> x; rewrite dlet1E /= dnull1E /= (@sumE_fin _ []). qed.

lemma eq_dlet ['a 'b] (F1 F2 : 'a -> 'b distr) d1 d2 :
  d1 = d2 => F1 == F2 => dlet d1 F1 = dlet d2 F2.
proof. by move=> -> eq_F; congr; apply/fun_ext. qed.

lemma in_eq_dlet ['a 'b] (F1 F2 : 'a -> 'b distr) (d : _ distr) :
  (forall x, x \in d => F1 x = F2 x) => dlet d F1 = dlet d F2.
proof.
move=> eq_F; apply/eq_distr => b; rewrite !dlet1E.
apply: eq_sum => a /=; case: (mu1 d a = 0%r) => [->//|].
by move/supportP => /eq_F ->.
qed.

lemma mu_dlet_le ['a 'b 'c]
  (d : 'a distr) (F1 : 'a -> 'b distr) (F2 : 'a -> 'c distr) P1 P2 :
  (forall x, x \in d => mu (F1 x) P1 <= mu (F2 x) P2) =>
  mu (dlet d F1) P1 <= mu (dlet d F2) P2.
proof.
rewrite !dletE => h; apply ler_sum_pos => /=; 1: smt(mu_bounded).
by apply (@summable_le_pos _ (mu1 d)); [apply summable_mu1 | smt(mu_bounded)].
qed.

lemma dlet_ll ['a 'b] d f :
     is_lossless d => (forall x, x \in d => is_lossless (f x))
  => is_lossless (dlet<:'a, 'b> d f).
proof.
move=> ll_d ll_df; rewrite /is_lossless dlet_muE_swap /predT /=.
rewrite -(@eq_sum (fun a => mu1 d a * sum (mu1 (f a)))) /=.
- by move=> a; rewrite sumZ.
rewrite -(@eq_sum (fun a => mu1 d a)) /=.
- move=> a; case: (mu1 d a = 0%r) => [->//|].
  by move/supportP=> /ll_df @/is_lossless; rewrite muE => ->.
by move: ll_d; rewrite /is_lossless muE.
qed.

lemma finite_dlet ['a 'b] (d : 'a distr) (f : 'a -> 'b distr) :
     is_finite (support d)
  => (forall x, x \in d => is_finite (support (f x)))
  => is_finite (support (dlet<:'a, 'b> d f)).
proof.
pose J := flatten (map (fun x => to_seq (support (f x))) (to_seq (support d))).
move=> fin_d fin_f; apply: mkfinite; exists J.
move=> x /supportP; rewrite dlet1E; apply: contraR => xNJ.
apply: sum0_eq => a /=; case: (mu1 d a = 0%r) => [->//|].
rewrite -supportP => a_in_d; suff ->//: mu1 (f a) x = 0%r .
apply: contraR xNJ => /supportP x_in_fa @/J; apply/flatten_mapP.
by exists a; rewrite mem_to_seq // a_in_d /= mem_to_seq // &(fin_f).
qed.

lemma dlet_cst ['a 'b] (d1 : 'a distr) (d2 : 'b distr) :
  is_lossless d1 => dlet d1 (fun _ => d2) = d2.
proof.
move=> ll_d1; apply: eq_distr => x; rewrite dlet1E /=.
by rewrite sumZr -weightE ll_d1.
qed.


(* -------------------------------------------------------------------- *)
op dfold ['a] (f : int -> 'a -> 'a distr) (x : 'a) (i : int) =
  iteri i (fun k d => dlet d (f k)) (dunit x).

lemma dfold0 ['a] f x : dfold<:'a> f x 0 = dunit x.
proof. by apply: iteri0. qed.

lemma dfoldS ['a] f x i : 0 <= i =>
  dfold<:'a> f x (i + 1) = dlet (dfold f x i) (f i).
proof. by apply: iteriS. qed.

(* -------------------------------------------------------------------- *)
abbrev dlift (F: 'a -> 'b distr) : 'a distr -> 'b distr =
  fun d => dlet d F.

(* -------------------------------------------------------------------- *)
op dmap ['a 'b] (d : 'a distr) (f : 'a -> 'b) =
  dlet d (MUnit.dunit \o f).

lemma dlet_dunit ['a 'b] d (f : 'a -> 'b) : dlet d (dunit \o f) = dmap d f.
proof. by []. qed.

lemma dmap1E (d : 'a distr) (f : 'a -> 'b) (b : 'b):
  mu1 (dmap d f) b = mu d ((pred1 b) \o f).
proof.
rewrite dlet1E muE; apply/eq_sum=> x /=.
by rewrite MUnit.dunit1E /pred1 /(\o); case: (f x = b).
qed.

lemma dmap1E_can ['a 'b] (d : 'a distr) (f : 'a -> 'b) (g : 'b -> 'a) (b : 'b) :
     cancel g f
  => (forall a, a \in d => g (f a) = a)
  => mu1 (dmap d f) b = mu1 d (g b).
proof.
move=> can_fg can_gf; rewrite dmap1E &(mu_eq_support).
move=> a ad @/(\o) @/pred1; apply/eq_iff; split; last exact: canLR.
by move=> faE; move/can_gf: ad; rewrite faE.
qed.

lemma in_dmap1E_can (d: 'a distr) (f: 'a -> 'b) (g: 'b -> 'a) (x: 'b):
  f (g x) = x =>
  (forall (y: 'a), y \in d => f y = x => y = g x) => 
  mu1 (dmap d f) x = mu1 d (g x). 
proof.
rewrite dmap1E /= => can_fg local_can_gf.
apply mu_eq_support => y y_in_d @/(\o) @/pred1; apply/eq_iff.
split => [|->//].
by apply local_can_gf.
qed.

lemma dmapE (d : 'a distr) (f : 'a -> 'b) (P : 'b -> bool):
  mu (dmap d f) P = mu d (P \o f).
proof.
rewrite dlet_muE_swap muE.
apply/eq_sum=> a /=; rewrite (@sumE_fin _ [f a]) //=.
+ by move=> b; rewrite (@eq_sym b) MUnit.dunit1E; case: (f a = b).
+ by rewrite big_seq1 /= MUnit.dunit1E.
qed.

lemma supp_dmap (d : 'a distr) (f : 'a -> 'b) (b : 'b):
  b \in (dmap d f) <=> exists a, a \in d /\ b = f a.
proof.
rewrite supp_dlet /(\o); apply/exists_eq=> a /=.
by rewrite MUnit.supp_dunit.
qed.

lemma dmap_supp ['a 'b] (d : _ distr) f x :
  x \in d => f x \in dmap<:'a, 'b> d f.
proof. by move=> xd; apply/supp_dmap; exists x. qed.

lemma weight_dmap (d : 'a distr) (f : 'a -> 'b) :
  weight (dmap d f) = weight d.
proof. by rewrite (_: predT = preim f predT) // dmapE. qed.

lemma dmap_ll (d : 'a distr) (f : 'a -> 'b) :
  is_lossless d => is_lossless (dmap d f).
proof. by rewrite /is_lossless weight_dmap. qed.

lemma dmap_uni_in_inj (d : 'a distr) (f : 'a -> 'b) :
     (forall (x, y : 'a), x \in d => y \in d => f x = f y => x = y)
  => is_uniform d => is_uniform (dmap d f).
proof.
move=> finj_in duni x y /supp_dmap [a [ina ->]] /supp_dmap [b [inb ->]].
have eq: forall z, z \in d => mu d (pred1 (f z) \o f) = mu d (pred1 z).
+ move=> z inz; rewrite (@mu_eq_support d (pred1 (f z) \o f) (pred1 z)) //.
  move=> x0 inx0 @/(\o) @/pred1 /=; rewrite eq_iff=> />; exact/finj_in.
by rewrite !dmap1E !eq //; apply/duni.
qed.

lemma dmap_duniform ['a 'b] (f : 'a -> 'b) (s : 'a list) :
     (forall x y, x \in s => y \in s => f x = f y => x = y)
  => dmap (duniform s) f = duniform (map f s).
proof.
move=> inj_f; apply: eq_distr => x; rewrite dmap1E.
rewrite duniform1E; case: (x \in map f s)%List => /=.
- case/mapP=> y [ys ->]; rewrite -(@mu_eq_support _ (pred1 y)).
  - move=> z; rewrite supp_duniform => zs @/pred1 @/(\o).
    by apply: eq_iff; split=> [->//|];  apply: inj_f.
  by rewrite duniform1E ys /= in_undup_map // size_map.
- move=> xNfs; rewrite mu0_false // => y /supp_duniform /(map_f f).
  by apply: contraL => @/pred1 @/(\o) ->.
qed.

lemma dmap_duniform_uniq (f : 'a -> 'b) (s : 'a list) :
  uniq (map f s) => dmap (duniform s) f = duniform (map f s).
proof.
move=> uq_fs; have uq_s := uniq_map _ _ uq_fs.
suff: forall x y, x \in s => y \in s => f x = f y => x = y.
- by apply: dmap_duniform.
move=> x y xs ys; apply: contraLR => ne_xy.
have: perm_eq s (x :: y :: rem x (rem y s)).
- have := List.perm_to_rem x s xs => /perm_eq_trans; apply.
  apply: perm_cons; pose t := rem x s.
  have := List.perm_to_rem y t _; 1: by rewrite /t mem_rem_neq.
  move/perm_eq_trans; apply; apply/perm_cons => @/t; rewrite remC.
  by apply: perm_eq_refl.
by move/(perm_eq_map f)/perm_eq_uniq; rewrite uq_fs /#.
qed.

lemma dmap_uni (d : 'a distr) (f : 'a -> 'b) :
  injective f => is_uniform d => is_uniform (dmap d f).
proof. by move=> finj; apply dmap_uni_in_inj=> x y _ _; apply/finj. qed.

lemma dmap_funi (d : 'a distr) (f : 'a -> 'b) :
  bijective f => is_funiform d => is_funiform (dmap d f).
proof.
  move=> [g [@/cancel can1 can2]] duni x y;rewrite !dmap1E.
  have Heq: forall z, pred1 z \o f = pred1 (g z).
  + move=> z;apply fun_ext => z' @/(\o) @/pred1 /=.
    by apply eq_iff;split=> [<- | ->];rewrite ?can1 ?can2.
  by rewrite !Heq;apply duni.
qed.

lemma dmap_fu (d : 'a distr) (f : 'a -> 'b) :
  surjective f => is_full d => is_full (dmap d f).
proof.
move=> fsurj fu x; rewrite supp_dmap.
by have [a ->] := fsurj x; exists a => /=; apply: fu.
qed.

lemma dmap_fu_in ['a 'b] (d : 'a distr) (f : 'a -> 'b) :
     (forall b, exists a, a \in d /\ b = f a)
  => is_full (dmap d f).
proof. by move=> surj_f b; apply/supp_dmap/surj_f. qed.

lemma dmap_dunit ['a 'b] (f : 'a -> 'b) (x : 'a) :
  dmap (dunit x) f = dunit (f x).
proof. by apply/eq_distr=> y; rewrite dmap1E !dunitE. qed.

lemma dmap_id (d: 'a distr) : dmap d (fun x=>x) = d.
proof. by rewrite /dmap /(\o) dlet_d_unit. qed.

lemma dmap_comp ['a 'b 'c] (f : 'a -> 'b) (g : 'b -> 'c) d :
 dmap (dmap d f) g = dmap d (g \o f).
proof.
rewrite /dmap dlet_dlet &(eq_dlet) //=.
by move=> x @/(\o) /=; rewrite dlet_unit.
qed.

lemma dmap_dlet ['a 'b 'c] d f g :
  dmap<:'b, 'c> (dlet<:'a, 'b> d f) g = dlet d (fun a => dmap (f a) g).
proof. by apply: dlet_dlet. qed.

lemma dlet_dmap ['a 'b 'c] d f g :
  dlet<:'b, 'c> (dmap<:'a, 'b> d f) g = dlet d (fun a => g (f a)).
proof.
by rewrite /dmap dlet_dlet &(eq_dlet) // => x; rewrite dlet_unit.
qed.

lemma eq_dmap ['a 'b] d f g : f == g => dmap<:'a, 'b> d f = dmap d g.
proof.
by move=> eq_fg @/dmap; apply: eq_dlet => // x @/(\o); rewrite eq_fg.
qed.

lemma dmap_cst ['a 'b] (d : 'a distr) (b : 'b) :
  is_lossless d => dmap d (fun _ => b) = dunit b.
proof. apply: dlet_cst. qed.

lemma eq_dmap_in ['a 'b] (d : 'a distr) (f g : 'a -> 'b) :
  (forall x, x \in d => f x = g x) => dmap d f = dmap d g.
proof. by move=> eq_fg; apply: in_eq_dlet => x /eq_fg @/(\o) ->. qed.

lemma dmap_id_eq_in ['a] (d : 'a distr) f :
  (forall x, x \in d => f x = x) => dmap d f = d.
proof. by move/eq_dmap_in => ->; apply: dmap_id. qed.

(* -------------------------------------------------------------------- *)
abbrev dfst ['a 'b] (d : ('a * 'b) distr) = dmap d fst.
abbrev dsnd ['a 'b] (d : ('a * 'b) distr) = dmap d snd.

op iscoupling ['a 'b] da db (d : ('a * 'b) distr) =
  dfst d = da /\ dsnd d = db.

(* -------------------------------------------------------------------- *)
lemma iscpl_sym ['a 'b] da db d :
  iscoupling<:'a, 'b> da db d => iscoupling db da (dmap d pswap).
proof. by case=> ha hb @/iscoupling; rewrite !dmap_comp. qed.

(* -------------------------------------------------------------------- *)
lemma iscpl_weightL ['a 'b] da db d :
  iscoupling<:'a, 'b> da db d => weight da = weight d.
proof.
case=> ha _; rewrite !weightE (@sum_partition fst) 1:summable_mu1 /=.
apply: eq_sum=> a /=; move/(congr1 mu): ha; move/fun_ext/(_ (pred1 a)).
move => <-; rewrite dmap1E muE /pred1 /(\o).
by apply: eq_sum => x /=; rewrite (@eq_sym a).
qed.

(* -------------------------------------------------------------------- *)
lemma iscpl_weightR ['a 'b] da db d :
  iscoupling<:'a, 'b> da db d => weight db = weight d.
proof. by move=> /iscpl_sym/iscpl_weightL ->; rewrite weight_dmap. qed.

(* -------------------------------------------------------------------- *)
lemma iscpl_weight ['a 'b] da db d :
  iscoupling<:'a, 'b> da db d => weight da = weight db.
proof.
move=> h; apply: (@eq_trans _ (weight d)).
+ by apply/(@iscpl_weightL _ db).
+ by apply/eq_sym/(iscpl_weightR da).
qed.

(* -------------------------------------------------------------------- *)
lemma iscpl_muL ['a 'b] da db d E :
  iscoupling<:'a, 'b> da db d => mu da E = mu d (E \o fst).
proof. by case=> <- _; rewrite dmapE. qed.

(* -------------------------------------------------------------------- *)
lemma iscpl_muR ['a 'b] da db d E :
  iscoupling<:'a, 'b> da db d => mu db E = mu d (E \o snd).
proof. by case=> _ <-; rewrite dmapE. qed.

(* -------------------------------------------------------------------- *)
lemma iscpl_dunit ['a 'b] x y :
  iscoupling<:'a, 'b> (dunit x) (dunit y) (dunit (x, y)).
proof. by rewrite /iscoupling !dmap_dunit. qed.

(* -------------------------------------------------------------------- *)
lemma iscpl_dlet ['a 'b 'c 'd] da db d f g fg :
     iscoupling<:'a, 'b> da db d
  => (forall x y, (x, y) \in d => iscoupling (f x) (g y) (fg (x, y)))
  => iscoupling<: 'c, 'd> (dlet da f) (dlet db g) (dlet d fg).
proof.
move=> hcpl1 hcpl2 @/iscoupling; case: hcpl1 => <- <-.
rewrite /dmap !dlet_dlet; split; apply: in_eq_dlet => // -[a b] /= abd.
- by rewrite dlet_unit; case: (hcpl2 _ _ abd) => @/dmap -> _.
- by rewrite dlet_unit; case: (hcpl2 _ _ abd) => @/dmap _ ->.
qed.

(* -------------------------------------------------------------------- *)
lemma iscpl_dfold ['a 'b] (o : int -> 'a -> 'b -> 'a) d1 d2 d x1 x2 k :
  (forall i, 0 <= i < k => iscoupling (d1 i) (d2 i) (d i)) =>

  iscoupling
    (dfold (fun i x => dlet (d1 i) (fun a => dunit (o i x a))) x1 k)
    (dfold (fun i x => dlet (d2 i) (fun a => dunit (o i x a))) x2 k)
    (dfold (fun i (x : _ * _) =>
       (dlet (d i) (fun a : _ * _ => dunit (o i x.`1 a.`1, o i x.`2 a.`2)))) (x1, x2) k).
proof.
elim/natind: k => [k le0_k|k ge0_k ih] cpl_d.
- by rewrite /dfold !iteri0 // &(iscpl_dunit).
rewrite !dfoldS // &(iscpl_dlet); first by apply/ih=> i ?; apply/cpl_d=> /#.
move=> a1 a2 _ /=; apply/iscpl_dlet; first by apply: cpl_d=> /#.
by move=> b1 b2 _ /=; apply/iscpl_dunit.
qed.

(* -------------------------------------------------------------------- *)
abbrev [-printing] dapply (F: 'a -> 'b) : 'a distr -> 'b distr =
  fun d => dmap d F.

(* -------------------------------------------------------------------- *)
theory DScalar.
op mscalar (k : real) (m : 'a -> real) (x : 'a) = k * (m x).

lemma isdistr_mscalar k (m : 'a -> real):
  isdistr m => 0%r <= k <= inv (weight (mk m)) => isdistr (mscalar k m).
proof.
move=> distr_m [ge0_k le_k_Vm]; split=> @/mscalar.
  by move=> x; rewrite mulr_ge0 // ge0_isdistr.
move=> s uq_s; have := mu_le_weight (mk m) (mem s).
rewrite mu_mem -mulr_sumr; case: (k = 0%r) => [->//|nz_k].
have {ge0_k nz_k} lt0_k : 0%r < k by rewrite ltr_neqAle eq_sym.
rewrite -ler_pdivl_mull // mulr1 => le; move: (le_k_Vm).
have gt0_Vm := ltr_le_trans _ _ _ lt0_k le_k_Vm.
rewrite -ler_pinv 1?gtr_eqF // invrK => h; apply/(ler_trans _ _ h).
apply/(ler_trans _ _ le) => {h le}; apply/lerr_eq.
by rewrite undup_id //; apply/eq_bigr=> /= x _; rewrite muK.
qed.

op dscalar (k : real) (d : 'a distr) = mk (mscalar k (mu1 d)).

abbrev (\cdot) (k : real) (d : 'a distr) = dscalar k d.

lemma dscalar1E (k : real) (d : 'a distr) (x : 'a):
  0%r <= k <= inv (weight d) => mu1 (k \cdot d) x = k * mu1 d x.
proof.
move=> [ge0_k le1_k]; rewrite  muK //.
by rewrite isdistr_mscalar 1:isdistr_mu1 mkK.
qed.

lemma dscalarE (k : real) (d : 'a distr) (E : 'a -> bool):
  0%r <= k => k <= inv (weight d) =>
  mu (k \cdot d) E = k * mu d E.
proof.
move=> ge0_k k_le_weight; rewrite !muE.
rewrite -(@eq_sum (fun x => k * if E x then mu1 d x else 0%r)).
+ by move=> x /=; case: (E x) => //= _; rewrite dscalar1E.
by rewrite sumZ.
qed.

lemma dscalar0r ['a] k : k \cdot dnull<:'a> = dnull.
proof.
apply/eq_distr=> a; rewrite muK; last by rewrite /mscalar !dnull1E.
split => /=.
- by move=> {a}a @/mscalar; rewrite dnull1E.
- move=> s _; rewrite (@BRA.eq_bigr _ _ (fun _ => 0%r)).
  - by move=> a' /= _ @/mscalar; rewrite dnull1E.
  - by rewrite Bigreal.sumr_const.
qed.

lemma dscalar1 ['a] (d : 'a distr) : 1%r \cdot d = d.
proof.
case: (d = dnull) => [->|nz_d]; first by rewrite dscalar0r.
apply/eq_distr=> x; rewrite dscalar1E //=.
have nz_wd: weight d <> 0%r.
- by apply: contra nz_d; apply: weight_eq0_dnull.
by apply: invr_ge1 => //; rewrite ltr_neqAle eq_sym ge0_weight.
qed.

lemma weight_dscalar (k : real) (d : 'a distr):
  0%r <= k => k <= inv (weight d) =>
  weight (k \cdot d) = k * weight d.
proof. by move=> ge0_k k_le_weight; rewrite dscalarE. qed.

lemma supp_dscalar (k : real) (d : 'a distr) x:
  0%r < k => k <= inv (weight d) =>
  x \in (k \cdot d) <=> x \in d.
proof.
move=> gt0_k k_le_weight; rewrite /support dscalar1E 1:ltrW // /#.
qed.

lemma dscalar_fu (k : real) (d : 'a distr):
  0%r < k => k <= inv (weight d) =>
  is_full d => is_full (k \cdot d).
proof. by move=> gt0k gekw df x;rewrite supp_dscalar //;apply df. qed.

lemma dscalar_ll (d : 'a distr):
  0%r < weight d =>
  is_lossless (inv (weight d) \cdot d).
proof. move=> gt0;rewrite /is_lossless dscalarE // /#. qed.

lemma dscalar_uni (k : real) (d : 'a distr):
  0%r < k <= inv (weight d) => is_uniform d => is_uniform (k \cdot d).
proof.
move=> [gt0_k lek] Hu x y; rewrite !dscalar1E ?(@ltrW 0%r) //.
by rewrite !supp_dscalar // => /Hu H/H ->.
qed.

end DScalar.
export DScalar.

(* -------------------------------------------------------------------- *)
lemma dlet_cst_weight ['a 'b] da db :
  dlet<:'a, 'b> da (fun _ => db) = weight da \cdot db.
proof.
apply/eq_distr=> b; rewrite dlet1E /= sumZr -weightE.
case: (db = dnull) => [->|nz_db]; first by rewrite dscalar0r !dnull1E.
rewrite dscalar1E // ge0_weight /=; apply: (@ler_trans 1%r).
- by apply: le1_mu.
suff ?: weight db <> 0%r.
- by apply/invr_ge1/le1_mu => //; rewrite ltr_neqAle eq_sym ge0_weight.
by apply: contra nz_db; apply: weight_eq0_dnull.
qed.

(* -------------------------------------------------------------------- *)
op dscale ['a] (d : 'a distr) = dscalar (inv (weight d)) d.

lemma dscale1E ['a] (d : 'a distr) (x : 'a) :
  mu1 (dscale d) x = mu1 d x / weight d.
proof. by rewrite dscalar1E // invr_ge0 ge0_weight. qed.

lemma dscaleE ['a] (d : 'a distr) (E : 'a -> bool) :
  mu (dscale d) E = mu d E / weight d.
proof. by rewrite dscalarE // invr_ge0 ge0_weight. qed.

lemma weight_dscale ['a] (d : 'a distr) :
  weight (dscale d) = if weight d = 0%r then 0%r else 1%r.
proof.
rewrite weight_dscalar // 1:invr_ge0 1:ge0_weight.
by case: (weight d = 0%r)=> [->|/divrr].
qed.

lemma supp_dscale ['a] (d : 'a distr) x:
  x \in (dscale d) <=> x \in d.
proof.
case: (weight d <= 0%r)=> [le0_weight|/ltrNge gt0_weight].
+ rewrite (@weight_eq0_dnull d _).
  + by apply/ler_asym; rewrite le0_weight ge0_weight.
  rewrite !supp_dnull.
  by rewrite /support dscale1E dnull1E weight_dnull.
by apply/supp_dscalar=> //; exact/invr_gt0.
qed.

lemma dscale_ll ['a] (d : 'a distr) :
  0%r < weight d => is_lossless (dscale d).
proof. apply dscalar_ll. qed.

lemma dscale_uni ['a] (d : 'a distr) :
  is_uniform d => is_uniform (dscale d).
proof.
case: (weight d = 0%r) => Hw.
+ by move=> _ x y _ _; rewrite !dscale1E Hw.
apply: dscalar_uni=> //; split=> //.
by apply: invr_gt0; smt(ge0_mu).
qed.

(* -------------------------------------------------------------------- *)
op mopt (d : 'a distr) = oapp (mu1 d) (1%r - weight d).
op dopt (d : 'a distr) : 'a option distr = mk (mopt d).

lemma isdistr_mopt (d : 'a distr) : isdistr (mopt d).
proof.
have sum_mopt : summable (mopt d) by apply/summable_oapp/summable_mu1.
have mopt_ge0 : forall x, 0%r <= oapp (mu1 d) (1%r - weight d) x.
  by case; smt(mu_bounded).
split => [//|s uniq_s].
suff S: sum (mopt d) <= 1%r by apply: ler_trans S; apply ler_big_sum.
by rewrite /mopt sumD1_None // /(\o) /= -weightE /#.
qed.

lemma dopt1E (d : 'a distr) x : mu1 (dopt d) x = oapp (mu1 d) (1%r - weight d) x.
proof. by rewrite muK ?isdistr_mopt. qed.

lemma doptE (d : 'a distr) E :
  mu (dopt d) E =
  mu d (E \o Some) + (if E None then 1%r - weight d else 0%r).
proof.
rewrite !muE sumD1_None ?summable_cond ?summable_mu1 /= addrC; congr.
- by apply eq_sum => /= x; rewrite /(\o) dopt1E.
- by case (E None) => //=; rewrite dopt1E /predT /= -weightE.
qed.

lemma dopt_ll (d : 'a distr) : is_lossless (dopt d).
proof.
rewrite /is_lossless muE /predT /= sumD1_None ?(summable_mu1) /=.
rewrite dopt1E /= (@eq_sum _ (mu1 d)) //=; 2: by rewrite -weightE /#.
by move => ?; rewrite /(\o) dopt1E.
qed.

(* -------------------------------------------------------------------- *)
op mrestrict ['a] (d : 'a distr) (p : 'a -> bool) =
  fun x => if p x then mu1 d x else 0%r.

op drestrict ['a] d p = mk (mrestrict<:'a> d p).

lemma isdistr_mrestrict ['a] d p : isdistr (mrestrict<:'a> d p).
proof. split.
+ by move=> a; rewrite /mrestrict; case: (p a).
+ move=> J uqJ @/mrestrict; have h := le1_mu1_fin d _ uqJ.
  by apply/(ler_trans _ _ h)/ler_sum=> /= a _; case: (p a).
qed.

lemma drestrict1E ['a] d p x :
  mu1 (drestrict<:'a> d p) x = if p x then mu1 d x else 0%r.
proof. by rewrite  muK 1:&(isdistr_mrestrict). qed.

lemma drestrictE ['a] d p q : mu (drestrict<:'a> d p) q = mu d (predI p q).
proof. 
rewrite !muE &(eq_sum) /predI /= => a.
by rewrite drestrict1E; case: (q a); case: (p a).
qed.

lemma supp_drestrict ['a] d p x :
  x \in drestrict<:'a> d p <=> (x \in d) /\ p x.
proof.
rewrite supportP drestrict1E (@fun_if (fun z => z <> 0%r)) /=.
by rewrite supportP andbC.
qed.

lemma drestrictE_le ['a] d (p q : _ -> bool) :
  q <= p => mu (drestrict<:'a> d p) q = mu d q.
proof.
move=> le_qp; rewrite drestrictE &(mu_eq).
by move=> x @/predI; apply/eq_iff/andb_idl/le_qp.
qed.

lemma weight_drestrict ['a] (d:'a distr) P:
  weight (drestrict d P) = mu d P.
proof. by rewrite drestrictE (@mu_eq _ (predI _ _) P). qed.

theory DConditional.

op dcond (d : 'a distr) (p : 'a -> bool) = dscale (drestrict d p).

lemma dcond_supp (d: 'a distr) (p: 'a -> bool) (x: 'a):
  x \in dcond d p <=> x \in d /\ p x.
proof.
rewrite supp_dscale supp_drestrict => //.
qed.

lemma dcond_ll (d: 'a distr) (p: 'a -> bool):
  mu d p > 0%r => is_lossless (dcond d p).
proof.
move => ?; apply dscale_ll; smt(weight_drestrict).
qed.

(* Chain rule of probability *)
lemma dcondE (d : 'a distr) (p : 'a -> bool) (p' : 'a -> bool) :
  mu (dcond d p) p' = mu d (predI p p') / mu d p.
proof.
by rewrite dscaleE drestrictE weight_drestrict.
qed.

lemma dcond1E (d : 'a distr) (p : 'a -> bool) (x : 'a):
  mu1 (dcond d p) x = if p x then mu1 d x / mu d p else 0%r.
proof.
rewrite dcondE; case: (p x) => [pxT|pxF]; last by rewrite mu0_false /#.
by congr; apply mu_eq => /#.
qed.

lemma dcond_uni (d: 'a distr) P :
  is_uniform d => is_uniform (dcond d P).
proof.
move => d_uni x y /dcond_supp [xd px] /dcond_supp [yd py].
by rewrite !dcond1E px py /= (@d_uni x y).
qed.

lemma eq_dcond (d : 'a distr) (p q : 'a -> bool) : 
  (forall x, x \in d => p x = q x) => dcond d p = dcond d q.
proof.
move => eq_p_q; apply/eq_distr => x; rewrite !dcond1E.
case (x \in d) => [xd|xnd]; last by rewrite !(@mu0_false _ (pred1 x)) /#.
by rewrite eq_p_q // (mu_eq_support eq_p_q).
qed.

lemma mu_dcond_ge (d : 'a distr) (p : 'a -> bool) x :
  p x => mu1 d x <= mu1 (dcond d p) x.
proof.
move => p_x; rewrite dcond1E p_x /=. 
case (x \in d) => [x_d|]; last by move/supportPn => -> /#.
suff muP : 0%r < mu d p by rewrite ler_pdivl_mulr //; smt(mu_bounded).
by apply/witness_support; exists x.
qed.

lemma finite_dcond (d : 'a distr) (p : 'a -> bool) : 
  is_finite (support d) => is_finite (support (dcond d p)).
proof. by apply finite_leq => x /dcond_supp. qed.


lemma dcondZ (d: 'a distr) (P: 'a -> bool) :
  mu d P = 0%r <=> dcond d P = dnull.
proof.
split => ?.
- apply eq_distr => a; rewrite dnull1E.
  suff: a \notin (dcond d P) by smt(ge0_mu).
  rewrite dcond_supp; smt(mu_sub).
- have H: (mu (dcond d P) P = 0%r) by smt(dnullE).
  rewrite dcondE // in H.
  (* Looks stupid but somehow speeds up smt ... *)
  suff: predI P P = P by smt().
  smt().
qed.

lemma dcond_dnull (P: 'a -> bool) :
  dcond dnull P = dnull.
proof.
apply eq_distr; smt(dnull1E dcond_supp supp_dnull ge0_mu).
qed.

lemma marginal_sampling (d : 'a distr) (f : 'a -> 'b) :
  d = dlet (dmap d f) (fun b => dcond d (fun a => f a = b)).
proof.
apply eq_distr => a; rewrite dlet1E /=.
rewrite (@sumE_fin _ [f a]) ?big_seq1 //=; 1: smt(dcond1E).
rewrite dcond1E dmap1E /(\o) /pred1 -/(pred1 a) /=.
case (a \in d) => [a_d|]; 2: smt(ge0_mu).
suff : mu d (fun (a0 : 'a) => f a0 = f a) > 0%r; smt(mu_sub).
qed.

lemma dcond_dmap (d : 'a distr) (f : 'a -> 'b) (p : 'b -> bool) : 
  dcond (dmap d f) p = dmap (dcond d (p \o f)) f.
proof.
apply/eq_distr => y. rewrite dmap1E dcond1E dcondE !dmapE.
case (p y) => [py|npy]; last by rewrite mu0_false // /#.
by congr; apply mu_eq; smt().
qed.

end DConditional.
export DConditional.

(* -------------------------------------------------------------------- *)
op mprod ['a,'b] (ma : 'a -> real) (mb : 'b -> real) (ab : 'a * 'b) =
  (ma ab.`1) * (mb ab.`2).

lemma isdistr_mprod ['a 'b] ma mb :
  isdistr<:'a> ma => isdistr<:'b> mb => isdistr (mprod ma mb).
proof.
move=> isa isb; split=> [x|s uqs].
+ by apply/mulr_ge0; apply/ge0_isdistr.
(* FIXME: This instance should be in bigops *)
rewrite (@partition_big ofst _ predT _ _ (undup (unzip1 s))).
+ by apply/undup_uniq.
+ by case=> a b ab_in_s _; rewrite mem_undup map_f.
pose P := fun x ab => ofst<:'a, 'b> ab = x.
pose F := fun (ab : 'a * 'b) => mb ab.`2.
rewrite -(@eq_bigr _ (fun x => ma x * big (P x) F s)) => /= [x _|].
+ by rewrite mulr_sumr; apply/eq_bigr=> -[a b] /= @/P <-.
pose s' := undup _; apply/(@ler_trans (big predT (fun x => ma x) s')).
+ apply/ler_sum=> a _ /=; apply/ler_pimulr; first by apply/ge0_isdistr.
  rewrite -big_filter -(@big_map snd predT) le1_sum_isdistr //.
  rewrite map_inj_in_uniq ?filter_uniq //; case=> [a1 b1] [a2 b2].
  by rewrite !mem_filter => @/P @/ofst |>.
by apply/le1_sum_isdistr/undup_uniq.
qed.

op [opaque] (`*`) (da : 'a distr) (db : 'b distr) = 
  mk (mprod (mu1 da) (mu1 db)).
lemma dprod_def (da : 'a distr) (db : 'b distr):
  da `*` db = mk (mprod (mu1 da) (mu1 db)) by rewrite/(`*`).

lemma dprod1E (da : 'a distr) (db : 'b distr) a b:
  mu1 (da `*` db) (a,b) = mu1 da a * mu1 db b.
proof. by rewrite dprod_def muK // isdistr_mprod isdistr_mu1. qed.

lemma dprodE Pa Pb (da : 'a distr) (db : 'b distr):
    mu (da `*` db) (fun (ab : 'a * 'b) => Pa ab.`1 /\ Pb ab.`2)
  = mu da Pa * mu db Pb.
proof.
rewrite muE sum_pair /=; first by apply/summable_cond/summable_mu1.
pose Fa := fun a => if Pa a then mu1 da a else 0%r.
pose Fb := fun b => if Pb b then mu1 db b else 0%r.
pose F  := fun a => Fa a * sum Fb; rewrite (@eq_sum _ F) /= => [a|].
+ rewrite /F -sumZ; apply: eq_sum => /= b @/Fa @/Fb => {Fa Fb F}.
  by case: (Pa a); case: (Pb b) => //= _ _; rewrite dprod1E.
by rewrite /F sumZr !muE.
qed.

lemma dprodEl (da : 'a distr) (db : 'b distr) Pa : 
  mu (da `*` db) (fun (ab : 'a * 'b) => Pa ab.`1) = mu da Pa * weight db.
proof.
rewrite (@mu_eq _ _ (fun (ab : 'a * 'b) => Pa ab.`1 /\ predT ab.`2)) 1:/#.
by rewrite dprodE.
qed.

lemma dprodEr (da : 'a distr) (db : 'b distr) Pb : 
  mu (da `*` db) (fun (ab : 'a * 'b) => Pb ab.`2) = mu db Pb * weight da.
proof.
rewrite (@mu_eq _ _ (fun (ab : 'a * 'b) => predT ab.`1 /\ Pb ab.`2)) 1:/#.
by rewrite dprodE RField.mulrC.
qed.

lemma dprod_dunit ['a 'b] (x : 'a) (y : 'b) :
  dunit x `*` dunit y = dunit (x, y).
proof.
by apply: eq_distr => -[a b]; rewrite dprod1E !dunit1E /#.
qed.

lemma le_dprod_or (da : 'a distr) (db : 'b distr) Pa Pb : 
   mu (da `*` db) (fun (ab : 'a * 'b) => Pa ab.`1 \/ Pb ab.`2) <= 
   mu da Pa * weight db + mu db Pb * weight da.
proof.
pose Pa' (p : 'a * 'b) := Pa p.`1.
pose Pb' (p : 'a * 'b) := Pb p.`2.
rewrite (@mu_eq _ _ (predU Pa' Pb')) 1:/# mu_or dprodEl dprodEr.
smt(mu_bounded).
qed.

lemma supp_dprod (da : 'a distr) (db : 'b distr) ab:
  ab \in da `*` db <=> ab.`1 \in da /\ ab.`2 \in db.
proof.
by case: ab => a b /=; rewrite !supportP dprod1E; smt(mu_bounded).
qed.

lemma weight_dprod (da : 'a distr) (db : 'b distr):
  weight (da `*` db) = weight da * weight db.
proof.
pose F := fun ab : 'a * 'b => predT ab.`1 /\ predT ab.`2.
by rewrite (@mu_eq _ _ F) // dprodE.
qed.

lemma dprod_ll (da : 'a distr) (db : 'b distr):
  is_lossless (da `*` db) <=> is_lossless da /\ is_lossless db.
proof. by rewrite /is_lossless weight_dprod #smt:(mu_bounded). qed.

lemma dprod_ll_auto (da : 'a distr) (db : 'b distr):
  is_lossless da => is_lossless db => is_lossless (da `*` db).
proof. by rewrite dprod_ll. qed.

lemma dprod_uni (da : 'a distr) (db : 'b distr):
  is_uniform da => is_uniform db => is_uniform (da `*` db).
proof.
move=> da_uni db_uni [a b] [a' b']; rewrite !supp_dprod !dprod1E /=.
by case=> /da_uni ha /db_uni hb [/ha-> /hb->].
qed.

lemma dprod_funi (da : 'a distr) (db : 'b distr):
  is_funiform da => is_funiform db => is_funiform (da `*` db).
proof.
move=> da_uni db_uni [a b] [a' b']; rewrite !dprod1E.
by congr; [apply da_uni | apply db_uni].
qed.

lemma dprod_fu (da : 'a distr) (db : 'b distr):
  is_full (da `*` db) <=> (is_full da /\ is_full db).
proof.
(split=> [h|[ha hb]]; first split) => x.
+ by move: (h (x, witness)); rewrite supp_dprod.
+ by move: (h (witness, x)); rewrite supp_dprod.
+ by rewrite supp_dprod !(ha, hb).
qed.

lemma dprod_fu_auto (da : 'a distr) (db : 'b distr):
  is_full da => is_full db => is_full (da `*` db).
proof. by rewrite dprod_fu. qed.

hint solve 1 random : dprod_ll_auto dprod_funi dprod_fu_auto.

lemma dprod_dlet ['a 'b] (da : 'a distr) (db : 'b distr):
  da `*` db = dlet da (fun a => dlet db (fun b => dunit (a, b))).
proof.
apply/eq_distr; case=> a b; rewrite dprod1E dlet1E /=.
rewrite (@sumE_fin _ [a]) //= => [a'|].
+ rewrite dlet1E (@sumE_fin _ [b]) //= => [b'|].
  + by rewrite dunitE /pred1 /= mulf_eq0 /#.
  by rewrite big_seq1 /= dunitE !mulf_eq0 /#.
rewrite big_seq1 /= dlet1E  (@sumE_fin _ [b]) //= => [b'|].
+ by rewrite dunitE /pred1 /= mulf_eq0 /#.
by rewrite big_seq1 /= dunitE.
qed.

lemma finite_dprod (da : 'a distr) (db : 'b distr) : 
     is_finite (support da) 
  => is_finite (support db) 
  => is_finite (support (da `*` db)).
proof.
move=> *; rewrite dprod_dlet finite_dlet // => *.
by apply finite_dlet => // *; apply finite_dunit.
qed.

lemma dmap_dprod ['a1 'a2 'b1 'b2]
  (d1 : 'a1 distr ) (d2 : 'a2 distr )
  (f1 : 'a1 -> 'b1) (f2 : 'a2 -> 'b2)
:
    dmap d1 f1 `*` dmap d2 f2
  = dmap (d1 `*` d2) (fun xy : _ * _ => (f1 xy.`1, f2 xy.`2)).
proof.
apply/eq_distr=> -[b1 b2]; rewrite !dprod1E !dmap1E /(\o) /=.
by rewrite -dprodE &(mu_eq) /= => -[a1 a2] @/pred1 /=.
qed.

lemma dprod_partition
  ['a 'b] (E : 'a * 'b -> bool) (da : 'a distr) (db : 'b distr)
: mu (da `*` db) E = sum (fun a => mu db (fun b => E (a, b)) * mu1 da a).
proof.
rewrite dprod_dlet dletE &(eq_sum) => /= x; rewrite mulrC; congr.
by rewrite (@dlet_dunit db (fun b => (x,b))) dmapE.
qed.

lemma dmap_dprod_comp ['a1 'a2 'b1 'b2 'c]
  (d1 : 'a1 distr) (d2 : 'a2 distr) (f1 : 'a1 -> 'b1) (f2 : 'a2 -> 'b2) h :
    dmap (d1 `*` d2) (fun xy : _ * _ => h (f1 xy.`1) (f2 xy.`2))
  = dmap<:_, 'c> (dmap d1 f1 `*` dmap d2 f2) (fun xy : _ * _ => h xy.`1 xy.`2).
proof. by rewrite dmap_dprod !dmap_comp. qed.

lemma dmap_dprodL ['a 'b 'c] (d1 : 'a distr) (d2 : 'b distr) (f : 'a -> 'c) :
  dmap d1 f `*` d2 = dmap (d1 `*` d2) (fun xy : _ * _ => (f xy.`1, xy.`2)).
proof. by rewrite -{1}(@dmap_id d2) dmap_dprod. qed.

lemma dmap_dprodR ['a 'b 'c] (d1 : 'a distr) (d2 : 'b distr) (f : 'b -> 'c) :
  d1 `*` dmap d2 f = dmap (d1 `*` d2) (fun xy : _ * _ => (xy.`1, f xy.`2)).
proof. by rewrite -{1}(@dmap_id d1) dmap_dprod. qed.

lemma dmap_bij ['a 'b] (d1 : 'a distr) (d2: 'b distr) (f : 'a -> 'b) (g : 'b -> 'a) :
     (forall x, x \in d1 => f x \in d2)
  => (forall x, x \in d2 => mu1 d2 x = mu1 d1 (g x))
  => (forall a, a \in d1 => g (f a) = a)
  => (forall b, b \in d2 => f (g b) = b)
  => dmap d1 f = d2.
proof.
move=> eqf eqg can_gf can_fg; apply/eq_distr => b.
rewrite dmap1E /(\o) {1}/pred1; case: (b \in d2); last first.
+ move=> ^/supportPn ->; apply: contraR.
  by move=> /neq0_mu [a [/= h1 <-]]; apply: eqf.
move=> b_d2; rewrite eqg 1:// &(mu_eq_support) /pred1 /= => x x_d1.
by apply eq_iff; split => [<<- | ->>]; rewrite ?can_gf ?can_fg.
qed.

(* -------------------------------------------------------------------- *)
lemma dlet_swap ['a 'b 'c] (d1 : 'a distr) (d2 : 'b distr) (F : 'a -> 'b -> 'c distr):
    dlet d1 (fun x1 => dlet d2 (F x1))
  = dlet d2 (fun x2 => (dlet d1 (fun x1 => F x1 x2))).
proof.
apply/eq_distr => c; rewrite !dlet1E.
pose G a b := mu1 d1 a * mu1 d2 b * mu1 (F a b) c.
rewrite (@eq_sum _ (fun a => sum (fun b => G a b))) => [a /=|]. 
  by rewrite dlet1E -sumZ &(eq_sum) /= /G => b; ring.
rewrite (@eq_sum _ (fun b => sum (fun a => G a b))) => [b /=|]. 
  by rewrite dlet1E -sumZ &(eq_sum) /= /G => a; ring.
apply sum_swap'; apply: (@summableM_bound 1%r) => //.
  by apply (@summableM_prod (mu1 d1) (mu1 d2)); apply: summable_mu1.
by move => [x y] //=; smt(mu_bounded).
qed.

lemma dprodC ['a 'b] (d1 : 'a distr) (d2 : 'b distr) :
  d1 `*` d2 = dmap (d2 `*` d1) (fun (p : 'b * 'a) => (p.`2, p.`1)).
proof.
rewrite !dprod_dlet dlet_swap /dmap dlet_dlet &(eq_dlet) //= => b.
by rewrite dlet_dlet &(eq_dlet) //= => a; rewrite dlet_unit.
qed.

lemma dmap_dprodE ['a 'b 'c] d1 d2 f :
  dmap<:'a * 'b, 'c> (d1 `*` d2) f = dlet d1 (fun x => dmap d2 (fun y => f (x, y))).
proof.
rewrite dprod_dlet dmap_dlet &(eq_dlet) // => a /=.
by rewrite dmap_dlet &(eq_dlet) // => b /=; rewrite dmap_dunit.
qed.

lemma dmap_dprodE_swap ['a 'b 'c] d1 d2 f :
  dmap<:'a * 'b, 'c> (d1 `*` d2) f = dlet d2 (fun y => dmap d1 (fun x => f (x, y))).
proof.
rewrite dprodC dmap_comp dmap_dprodE &(eq_dlet) //.
by move=> b /=; apply: eq_dlet => // ?.
qed.

lemma dprod_marginalL ['a 'b 'c] (da : 'a distr) (db : 'b distr) (f : 'a -> 'c) :
    dmap (da `*` db) (fun ab : 'a * 'b => f ab.`1)
  = weight db \cdot dmap da f.
proof. by rewrite dmap_dprodE_swap /= dlet_cst_weight. qed.

lemma dprod_marginalR ['a 'b 'c] (da : 'a distr) (db : 'b distr) (f : 'b -> 'c) :
    dmap (da `*` db) (fun ab : 'a * 'b => f ab.`2)
  = weight da \cdot dmap db f.
proof. by rewrite dmap_dprodE /= dlet_cst_weight. qed.

lemma dprod_dmap_cross ['a 'b 'c 'd 'e 'ab 'ac 'bd 'cd]
  (da : 'a distr) (db : 'b distr) (dc : 'c distr) (dd : 'd distr)
  (Fab : 'a * 'b -> 'ab)
  (Fcd : 'c * 'd -> 'cd)
  (F   : 'ab -> 'cd -> 'e)
  (Fac : 'a * 'c -> 'ac)
  (Fbd : 'b * 'd -> 'bd)
  (G   : 'ac -> 'bd -> 'e)
:
  (forall a b c d, F (Fab (a, b)) (Fcd (c, d)) = G (Fac (a, c)) (Fbd (b, d))) =>

  dlet
    (dmap (da `*` db) Fab)
    (fun ab =>
      dmap
        (dmap (dc `*` dd) Fcd)
        (fun cd => F ab cd))
  = dlet
      (dmap (da `*` dc) Fac)
      (fun ac =>
        dmap
          (dmap (db `*` dd) Fbd)
          (fun bd => G ac bd)).
proof.
pose D1 := dlet (da `*` db)
  (fun ab => dlet dc (fun c => dmap dd (fun d => F (Fab ab) (Fcd (c, d))))).
move=> eq; rewrite dlet_dmap /= &(eq_trans D1) /D1 => {D1}.
- by rewrite &(eq_dlet) // => ab /=; rewrite dmap_comp dmap_dprodE.
pose D2 := dlet (da `*` dc)
  (fun ac => dlet db (fun b => dmap dd (fun d => G (Fac ac) (Fbd (b, d))))).
rewrite dlet_dmap /= &(eq_trans D2) /D2 => {D2}; last first.
- by rewrite &(eq_dlet) // => ac /=; rewrite dmap_comp dmap_dprodE.
rewrite !dprod_dlet !dlet_dlet /= &(eq_dlet) // => a /=.
rewrite dlet_dlet /= dlet_swap &(eq_dlet) // => b /=.
rewrite 2!(dlet_dunit, dlet_unit) /= dlet_dmap.
rewrite &(eq_dlet) // => c /=; rewrite &(eq_dmap) // => d /=.
by apply: eq.
qed.

lemma dprod_cross ['a 'b 'c 'd 'e]
  (da : 'a distr) (db : 'b distr) (dc : 'c distr) (dd : 'd distr)
  (F  : 'a -> 'b -> 'c -> 'd -> 'e)
:
  dlet
    (da `*` db)
    (fun ab : 'a * 'b =>
      dmap
        (dc `*` dd)
        (fun cd : 'c * 'd => F ab.`1 ab.`2 cd.`1 cd.`2))
  = dlet
      (da `*` dc)
      (fun ac : 'a * 'c =>
        dmap
          (db `*` dd)
          (fun bd : 'b * 'd => F ac.`1 bd.`1 ac.`2 bd.`2)).
proof.
pose F1 (ab : 'a * 'b) (cd : 'c * 'd) := F ab.`1 ab.`2 cd.`1 cd.`2.
pose F2 (ac : 'a * 'c) (bd : 'b * 'd) := F ac.`1 bd.`1 ac.`2 bd.`2.
have := dprod_dmap_cross da db dc dd idfun idfun F1 idfun idfun F2 _.
- by move=> *; reflexivity. by rewrite !dmap_id.
qed.

(* -------------------------------------------------------------------- *)
op [opaque] djoin (ds : 'a distr list) : 'a list distr =
 foldr
   (fun d1 dl => dapply (fun xy : _ * _ => xy.`1 :: xy.`2) (d1 `*` dl))
   (dunit []) ds.
lemma djoin_axE (ds : 'a distr list): djoin ds = foldr
   (fun d1 dl => dapply (fun xy : _ * _ => xy.`1 :: xy.`2) (d1 `*` dl))
   (dunit []) ds by rewrite/djoin.

abbrev djoinmap ['a 'b] (d : 'a -> 'b distr) xs = djoin (map d xs).

lemma djoin_nil ['a]: djoin<:'a> [] = dunit [].
proof. by rewrite djoin_axE. qed.

lemma djoin_cons (d : 'a distr) (ds : 'a distr list):
 djoin (d :: ds) = dapply (fun xy : _ * _ => xy.`1 :: xy.`2) (d `*` djoin ds).
proof. by rewrite !djoin_axE. qed.

hint rewrite djoinE : djoin_nil djoin_cons.

lemma djoin1E (ds : 'a distr list) xs: mu1 (djoin ds) xs =
  if   size ds = size xs
  then BRM.big predT (fun xy : _ * _ => mu1 xy.`1 xy.`2) (zip ds xs)
  else 0%r.
proof.
elim: ds xs => [|d ds ih] xs /=; 1: rewrite djoin_nil dunitE.
+ by case: xs => [|x xs] /=; [rewrite BRM.big_nil | rewrite add1z_neqC0 1:size_ge0].
rewrite djoin_cons /= dmap1E /(\o) /=; case: xs => [|x xs] /=.
+ by rewrite add1z_neq0 1:size_ge0 /= mu0_false.
rewrite -(@mu_eq _ (pred1 (x, xs))).
+ by case=> y ys @/pred1 /=.
rewrite dprod1E ih BRM.big_cons /predT /=; pose B := BRM.big _ _ _.
by rewrite (@fun_if (( * ) (mu1 d x))) /= /#.
qed.

lemma djoin_nil1E (ds : 'a list):
  mu1 (djoin []) ds = b2r (ds = []).
proof. by rewrite djoinE /= dunit1E (@eq_sym ds). qed.

lemma djoin_cons1E (d : 'a distr) (ds : 'a distr list) x xs :
  mu1 (djoin (d :: ds)) (x :: xs) = mu1 d x * mu1 (djoin ds) xs.
proof. by rewrite /= djoin_cons /= dmap1E -dprod1E &(mu_eq) => -[] /#. qed.

lemma djoin_cons1nilE (d : 'a distr) (ds: ('a distr) list):
  mu1 (djoin (d::ds)) [] = 0%r.
proof. by rewrite djoin1E /= add1z_neq0 //= size_ge0. qed.

lemma supp_djoin (ds : 'a distr list) xs : xs \in djoin ds <=>
  size ds = size xs /\ all (fun (xy : _ * _) => support xy.`1 xy.`2) (zip ds xs).
proof.
rewrite supportP djoin1E; case: (size ds = size xs) => //= eq_sz; split.
+ apply: contraR; rewrite -has_predC => /hasP[] @/predC [d x] /=.
  case=> hmem xNd; apply/prodr_eq0; exists (d, x) => @/predT /=.
  by rewrite hmem /= -supportPn.
+ apply: contraL => /prodr_eq0[] @/predT [d x] /= [hmem xNd].
  rewrite -has_predC &(hasP); exists (d, x).
  by rewrite hmem /predC /= supportPn.
qed.

lemma supp_djoin_cons ['a] us d ds :
  us \in djoin<:'a> (d :: ds) =>
    exists v vs, v \in d /\ vs \in djoin ds.
proof.
move/supp_djoin => /=; case: us => /= [|u us]; first smt(size_ge0).
case=> /addzI => eqsz [ud hall]; exists u us.
by split=> //; apply/supp_djoin.
qed.

lemma supp_djoin_size (ds : 'a distr list) xs :
  xs \in djoin ds => size xs = size ds.
proof. by case/supp_djoin=> ->. qed.

lemma djoin_cat ['a] ds1 ds2 : djoin<:'a> (ds1 ++ ds2) =
  dmap (djoin ds1 `*` djoin ds2) (fun xs : _ * _ => xs.`1 ++ xs.`2).
proof.
elim: ds1 => /= [| d ds1 ih].
- rewrite djoin_nil dprod_dlet dlet_unit /= dlet_dunit /=.
  by rewrite dmap_comp /(\o) /= dmap_id.
rewrite djoin_cons /= dmap_dprodE_swap /= ih dmap_dprodE_swap.
rewrite  dlet_dlet eq_sym dmap_dprodE_swap &(eq_dlet) // => xs /=.
rewrite djoin_cons /= dmap_dprodE_swap /= dmap_dlet dlet_dmap.
by apply: eq_dlet => // ys /=; rewrite dmap_comp &(eq_dlet) // => ?.
qed.

lemma djoin_perm_s1s ['a] ds1 d ds2 :
  djoin<:'a> (ds1 ++ d :: ds2) =
    dlet (djoin ds1 `*` djoin ds2)
      (fun ds : _ * _ => dmap d (fun x => ds.`1 ++ x :: ds.`2)).
proof.
rewrite djoin_cat dmap_dprodE dprod_dlet dlet_dlet &(eq_dlet) //= => xs1.
rewrite djoin_cons /= dmap_dprodE_swap dlet_dlet dmap_dlet &(eq_dlet) //= => xs2.
by rewrite dmap_comp dlet_unit /=.
qed.

lemma djoin_seq1 ['a] d : djoin<:'a> [d] = dmap d (fun x => [x]).
proof.
by rewrite djoin_cons /= djoin_nil dmap_dprodE_swap dlet_unit.
qed.

lemma djoin_rcons ['a] ds d : djoin<:'a> (rcons ds d) =
  dmap (djoin ds `*` d) (fun xsx : _ * _ => rcons xsx.`1 xsx.`2).
proof.
rewrite -cats1 djoin_cat djoin_seq1 !dmap_dprodE &(eq_dlet) //.
move=> xs /=; rewrite dmap_comp &(eq_dlet) //.
by move=> z @/(\o) /=; rewrite cats1.
qed.

lemma weight_djoin (ds : 'a distr list) :
  weight (djoin ds) = BRM.big predT weight ds.
proof.
elim: ds => [|d ds ih]; rewrite djoinE /=.
+ by rewrite dunit_ll BRM.big_nil.
+ by rewrite weight_dmap weight_dprod BRM.big_cons -ih.
qed.

lemma djoin_ll (ds : 'a distr list):
  (forall d, d \in ds => is_lossless d) => is_lossless (djoin ds).
proof.
move=> ds_ll; rewrite /is_lossless weight_djoin.
rewrite BRM.big_seq -(@BRM.eq_bigr _ (fun _ => 1%r)) /=.
+ by move=> d /ds_ll ll_d; apply/eq_sym.
+ by rewrite -(@BRM.big_seq _ ds) mulr_const RField.expr1z.
qed.

lemma weight_djoin_nil: weight (djoin<:'a> []) = 1%r.
proof. by rewrite weight_djoin BRM.big_nil. qed.

lemma weight_djoin_cons d (ds:'a distr list):
  weight (djoin (d :: ds)) = weight d * weight (djoin ds).
proof. by rewrite weight_djoin BRM.big_cons -weight_djoin. qed.

lemma djoin_nilE P : mu (djoin<:'a> []) P = b2r (P []).
proof. by rewrite djoin_nil // dunitE. qed.

lemma djoin_consE (dflt:'a) (d: 'a distr) ds P Q :
    mu
      (djoin (d :: ds))
      (fun xs => P (head dflt xs) /\ Q (behead xs))
  = mu d P * mu (djoin ds) Q.
proof. by rewrite djoin_cons /= dmapE dprodE. qed.

lemma djoin_fu (ds : 'a distr list) (xs : 'a list):
     size ds = size xs
  => (forall d x, d \in ds => x \in d)
  => xs \in djoin ds.
proof.
move=> eq_sz hfu; rewrite supportP djoin1E eq_sz /=.
rewrite RealOrder.gtr_eqF // Bigreal.prodr_gt0_seq.
case=> d x /= /mem_zip [d_ds x_xs] _.
by rewrite -/(_ \in _) supportP -supportPn /=; apply: hfu.
qed.

lemma djoin_uni (ds:'a distr list):
  (forall d, d \in ds => is_uniform d) => is_uniform (djoin ds).
proof.
elim: ds => [|d ds ih] h //=; rewrite !djoinE; 1: by apply/dunit_uni.
rewrite dmap_uni => [[x xs] [y ys] //=|].
apply: dprod_uni; [apply/h | apply/ih] => //.
by move=> d' hd'; apply/h => /=; rewrite hd'.
qed.

lemma djoin_dmap ['a 'b 'c] (d : 'a -> 'b distr) (xs : 'a list) (f : 'b -> 'c):
  dmap (djoin (map d xs)) (map f) = djoin (map (fun x => dmap (d x) f) xs).
proof.
elim: xs => /= [|x xs ih]; first by rewrite !djoinE ?dmap_dunit.
by rewrite !djoin_cons -ih /= dmap_dprod /= !dmap_comp.
qed.

lemma djoin_dmap_nseq ['a 'b] n (d : 'a distr) (f : 'a -> 'b) :
  dmap (djoin (nseq n d)) (map f) = djoin (nseq n (dmap d f)).
proof.
elim/natind: n => [n le0_n|].
- by rewrite !nseq0_le //= !djoin_nil dmap_dunit.
move=> n ge0_n ih; rewrite !nseqS // !djoin_cons /= -ih.
by rewrite -dmap_dprod_comp dmap_comp.
qed.

lemma supp_djoinmap ['a 'b] (d : 'a -> 'b distr) xs ys:
  ys \in djoinmap d xs <=> size xs = size ys /\
    all (fun xy => support (d (fst xy)) (snd xy)) (zip xs ys).
proof.
rewrite supp_djoin size_map; congr; apply/eq_iff.
by rewrite zip_mapl all_map &(eq_all).
qed.

lemma le_djoin_size (ds : 'a distr list) (x : 'a) r: 
  (forall d y, d \in ds => mu1 d y <= r) =>
  mu (djoin ds) (fun s : 'a list => x \in s) <= (size ds)%r * r.
proof.
elim: ds => [|d ds IHds bound_ds]; first by rewrite djoin_nil dunitE.
rewrite djoin_cons /= dmapE /(\o). 
rewrite (@mu_eq _ _ (fun (p : 'a * 'a list) => p.`1 = x \/ x \in p.`2)) 1:/#.
have E := le_dprod_or d (djoin ds) (pred1 x) (fun xs : 'a list => x \in xs).
apply (@ler_trans _ _ _ E) => {E}. 
apply (ler_trans (mu1 d x + mu (djoin ds) (fun (xs : 'a list) => x \in xs))). 
- (* FIXME: smt(mu_bounded) should be enough? *)
  apply ler_add; apply ler_pimulr; smt(mu_bounded). 
rewrite fromintD mulrDl /=; apply ler_add; first by apply bound_ds.
by apply IHds => /#.
qed.

lemma djoinmap_dlet (d1 : 'a -> 'b distr) (d2: 'a -> 'b -> 'c distr) xs : 
djoinmap (fun x => dlet (d1 x) (d2 x)) xs = 
dlet (djoinmap d1 xs) (fun x1s => djoinmap (fun (p:_*_) => d2 p.`1 p.`2) (zip xs x1s)).
proof.
elim: xs.
+ by rewrite !djoin_nil dlet_unit /= djoin_nil.
move=> x l hrec /=.
rewrite !djoin_cons dprod_dlet dlet_dmap dprod_dlet !dlet_dlet /= dmap_dlet.
apply eq_dlet => // b /=.
rewrite dlet_dunit dlet_dmap dmap_dlet /=.
have -> : 
  (fun (a : 'b list) =>
     djoin (d2 x b :: map (fun (p : 'a * 'b) => d2 p.`1 p.`2) (zip l a))) = 
  (fun (a : 'b list) =>
     dlet (d2 x b) 
       (fun xy1 => dmap (djoin (map (fun (p : 'a * 'b) => d2 p.`1 p.`2) (zip l a)))
                        (fun xy2 => xy1::xy2))).
+ by apply fun_ext => lb; rewrite djoin_cons /= dmap_dprodE. 
rewrite dlet_swap; apply eq_dlet => //= xy1.
rewrite dmap_dlet hrec dlet_dlet; apply eq_dlet => //= lb.
by apply eq_dlet => //= xy2; rewrite dmap_dunit.
qed.

(* -------------------------------------------------------------------- *)
op madd ['a] (df dg : 'a distr) = fun x => mu1 df x + mu1 dg x.

lemma isdistr_madd (df dg : 'a distr) :
  weight df + weight dg <= 1%r => isdistr (madd df dg).
proof.
move=> le1_wD; split; first by move=> x @/madd; rewrite addr_ge0.
move=> s uq_s @/madd; rewrite big_split.
apply/(ler_trans _ _ le1_wD)/ler_add;
  by rewrite !muE &(ler_big_sum) // &(summable_mu1).
qed.

op (+) ['a] (df dg : 'a distr) = mk (madd df dg).

lemma dadd1E ['a] (df dg : 'a distr) x :
  weight df + weight dg <= 1%r => mu1 (df + dg) x = mu1 df x + mu1 dg x.
proof. by move=> le1_wD; rewrite muK // &(isdistr_madd). qed.

lemma daddE ['a] (df dg : 'a distr) x :
  weight df + weight dg <= 1%r => mu (df + dg) x = mu df x + mu dg x.
proof. 
move=> le1_wD; rewrite !muE -sumD 1,2:&(summable_mu1_cond) /=.
by apply: eq_sum=> y /=; case: (x y) => // _; rewrite dadd1E.
qed.

(* -------------------------------------------------------------------- *)
abstract theory MUniFinFun.
type t.

clone FinType as FinT with type t <- t.

op mfun ['u] (d : t -> 'u distr) (f : t -> 'u) =
  BRM.big predT (fun x => mu1 (d x) (f x)) FinT.enum.

lemma mfunE ['u] (d : t -> 'u distr) (f : t -> 'u) :
  mfun d f = mu1 (djoin (map d FinT.enum)) (map f FinT.enum).
proof.
rewrite /mfun djoin1E !size_map /=; pose h x := (d x, f x).
pose s := zip _ _; have ->: s = map h FinT.enum.
- by rewrite /s zip_map zipss -map_comp.
by rewrite BRM.big_map &(BRM.eq_bigr). 
qed.

lemma isdistr_dfun ['u] (d : t -> 'u distr) : isdistr (mfun d).
proof.
pose F f := mu1 (djoin (map d FinT.enum)) (map f FinT.enum).
rewrite (@eq_isdistr _ F) 1:&(mfunE) /F.
apply/(@isdistr_comp (mu1 (djoinmap d _)))/isdistr_mu1.
move=> f g eq; apply/fun_ext=> x; pose i := index x FinT.enum.
move/(congr1 (fun s => nth witness s i)): eq => /=.
have rgi: 0 <= i < size FinT.enum.
- by rewrite index_ge0 index_mem FinT.enumP.
rewrite !(@nth_map witness) //.
by rewrite !nth_index ?FinT.enumP.
qed.

op dfun ['u] (d : t -> 'u distr) = mk (mfun d).

lemma dfun1E ['u] (d : t -> 'u distr) f :
  mu1 (dfun d) f = BRM.big predT (fun x => mu1 (d x) (f x)) FinT.enum.
proof.
by rewrite muK 1:isdistr_dfun &(BRM.eq_bigr).
qed.

lemma dfun1E_djoin ['u] (d : t -> 'u distr) f :
  mu1 (dfun d) f = mu1 (djoinmap d FinT.enum) (map f FinT.enum).
proof. by rewrite muK 1:isdistr_dfun mfunE. qed.

op tofun ['u] (us : 'u list) =
  fun x => nth witness us (index x FinT.enum).

op offun (f : t -> 'u) =
  map f FinT.enum.

lemma offunK ['u] : cancel offun<:'u> tofun.
proof.
move=> f; apply/fun_ext => x; rewrite /tofun (@nth_map witness).
- by rewrite index_ge0 index_mem FinT.enumP.
- by rewrite nth_index 1:FinT.enumP.
qed.

lemma tofunK ['u] us :
  size us = FinT.card => offun<:'u> (tofun us) = us.
proof.
move=> sz_us; apply/(eq_from_nth witness).
- by rewrite size_map sz_us.
rewrite size_map -/FinT.card => i rg_i.
rewrite /offun (@nth_map witness) // /tofun.
by rewrite index_uniq // FinT.enum_uniq.
qed.

lemma dfun_dmap ['u] (d : t -> 'u distr) : 
  dfun d = dmap (djoinmap d FinT.enum) tofun.
proof.
apply: eq_distr => f; rewrite dfun1E_djoin dmap1E /(\o) /pred1.
apply: mu_eq_support => l /supp_djoinmap [hsz _] /=.
apply eq_iff; split => [-> | <-]; first by apply offunK.
by rewrite -/(offun (tofun l)) tofunK // -hsz.
qed.

lemma dfun_supp ['u] (d : t -> 'u distr) (f : t -> 'u) :
  f \in dfun d <=> (forall x, f x \in d x).
proof.
rewrite supportP dfun1E -prodr_eq0 negb_exists /=; split;
  by move=> + x - /(_ x); rewrite FinT.enumP /predT /= supportP.
qed.

lemma dfun_fu ['u] (d : t -> 'u distr) :
  (forall x, is_full (d x)) => is_full (dfun d).
proof. by move=> fud f; apply/dfun_supp=> x; apply/fud. qed.

lemma dfun_uni ['u] (d : t -> 'u distr) :
  (forall x, is_uniform (d x)) => is_uniform (dfun d).
proof.
move=> unid f g fd gd; rewrite !dfun1E_djoin &(djoin_uni).
- by move=> d' /mapP[x [_ ->]]; apply: unid.
- apply: supp_djoinmap; rewrite size_map /=; apply/allP.
  by case=> x y /= /mem_zip_mapr [_ ->]; apply/dfun_supp.
- apply: supp_djoinmap; rewrite size_map /=; apply/allP.
  by case=> x y /= /mem_zip_mapr [_ ->]; apply/dfun_supp.
qed.

lemma dfun_funi ['u] (d : t -> 'u distr) :
     (forall x, is_uniform (d x))
  => (forall x, is_full (d x))
  => is_funiform (dfun d).
proof.
move=> funi_d full_d; apply: is_full_funiform.
- by apply/dfun_fu/full_d.
- by apply/dfun_uni.
qed.

lemma dfunE_djoin ['u] du (E : (t -> 'u) -> bool) : mu (dfun du) E =
  mu (djoinmap du FinT.enum) (E \o tofun).
proof.
rewrite -dmapE; congr; apply/eq_distr=> f.
rewrite dfun1E_djoin dmap1E &(mu_eq_support) /pred1.
move=> us /supp_djoinmap [/eq_sym sz_us /allP h] @/(\o) /=.
apply/eq_iff; split => [->|]; first by apply/offunK.
by move/(congr1 offun); rewrite tofunK.
qed.

lemma dfunE ['u] du (p : t -> 'u -> bool) :
    mu (dfun du) (fun (f : t -> 'u) => forall x, p x (f x))
  = BRM.big predT (fun x => mu (du x) (p x)) FinT.enum.
proof.
pose P f := all (fun x => p x (f x)) FinT.enum.
rewrite -(@mu_eq _ P) => [f|] @/P; first rewrite allP /=.
- by apply: eq_iff; split=> h *; apply: h; rewrite FinT.enumP.
rewrite dfunE_djoin /(\o) /tofun; have {P} := FinT.enum_uniq.
pose P xs us := all (fun x => p x (nth witness us (index x xs))) xs.
rewrite -/(P FinT.enum); elim: FinT.enum => [|x xs ih].
- by rewrite djoin_nilE /= BRM.big_nil.
case=> x_xs uq_xs; rewrite map_cons /=.
pose Q us := p x (head witness us) /\ P xs (behead us).
rewrite -(@mu_eq_support _ Q) => [us /supp_djoin_cons|].
- case=> v vs [v_dux /supp_djoin []]; rewrite size_map.
  move=> sz_xs hall @/Q @/P /=; rewrite index_head nth0_head.
  congr; apply/eq_iff/eq_all_in=> /= x' x'_xs.
  case: (x' = x) => [->>//|]; rewrite index_cons.
  by move=> ->; rewrite nth_behead ?index_ge0.
by rewrite (@djoin_consE _ _ _ (p x) (P xs)) ih.
qed.

lemma weight_dfun ['u] (df : t -> 'u distr) :
  weight (dfun df) = BRM.big predT (fun x => weight (df x)) FinT.enum.
proof. by have /= -> := dfunE df (fun _ _ => true). qed.

lemma dfun_ll ['u] (d : t -> 'u distr) :
  (forall x, is_lossless (d x)) => is_lossless (dfun d).
proof.
move=> d_ll; rewrite /is_lossless weight_dfun.
apply BRM.big1 => * /=; apply d_ll.
qed.

lemma dlet_dfun (d1 : t -> 'u distr) (d2 : t -> 'u -> 'v distr) : 
  dlet (dfun d1) (fun f1 => dfun (fun (x:t) => d2 x (f1 x))) = 
  dfun (fun x => dlet (d1 x) (fun x1 => d2 x x1)).
proof.
rewrite !dfun_dmap /= dlet_dmap djoinmap_dlet dmap_dlet.
apply in_eq_dlet => //= l /supp_djoinmap [hsz hall].
rewrite dfun_dmap; apply eq_dlet => //.
congr; apply (eq_from_nth witness); 1: by rewrite !size_map size_zip hsz.
move=> i; rewrite size_map => hi.
rewrite (@nth_map witness) 1:// /=.
rewrite (@nth_map (witness, witness)) 1:size_zip 1:-hsz 1:// /=.
rewrite (@nth_zip witness witness) //= /tofun index_uniq // FinT.enum_uniq.
qed.

lemma dfun_unit (f : t -> 'u) : dfun (fun x => dunit (f x)) = dunit f. 
proof.
apply eq_distr => g; rewrite dunit1E dfun1E /=.
case (f = g) => [<- | f_neq_g].
+ by rewrite BRM.big1 // => x _ /=; rewrite dunit1E.
move: f_neq_g; rewrite fun_ext negb_forall=> /= - [x hx].
by rewrite (@BRM.bigD1 _ _ x) 1:FinT.enumP 1:FinT.enum_uniq /= dunit1E hx.
qed.

lemma dmap_dfun (d : t -> 'u distr) (F: t -> 'u -> 'v) :  
  dmap (dfun d) (fun f x => F x (f x)) =
  dfun (fun x => dmap (d x) (fun fx => F x fx)).
proof. 
by rewrite /dmap -dlet_dfun /=; apply eq_dlet => // f; rewrite dfun_unit.
qed.

lemma dfun1E_fix1 ['u] (d : t -> 'u distr) x0 f :
  mu1 (dfun d) f = mu1 (d x0) (f x0) * mu1 (dfun d.[x0 <- dunit (f x0)]) f.
proof.
apply/eq_sym; rewrite dfun1E (@BRM.bigD1 _ _ x0) ?(FinT.enumP, FinT.enum_uniq) /=.
rewrite !fupdate_eq dunit1E /= -(@BRM.eq_bigr _ (fun x => mu1 (d x) (f x))) /=.
- by move=> x @/predC1 ne_x_x0; rewrite !fupdate_neq 1,2:eq_sym.
have /= <- := (BRM.bigD1 (fun x => mu1 (d x) (f x)) FinT.enum x0 _ _).
- by apply: FinT.enumP.
- by apply: FinT.enum_uniq.
- by rewrite -dfun1E.
qed.

lemma dlet_dfun_fupdate_ll ['u] (d : t -> 'u distr) x0 v :
  dlet
    (dfun d.[x0 <- dunit v])
    (fun f => dmap (d x0) (fun y => f.[x0 <- y]))
  = dfun d.
proof.
pose F (fy : (t -> 'u) * _) := fy.`1.[x0 <- fy.`2].
rewrite -(@dmap_dprodE _ _ F) dmap_dprodE_swap /F /= => {F}.
apply/eq_distr=> f; rewrite dlet1E dfun1E /=.
rewrite (@sumD1 _ (f x0)) /=; first apply: summable_mu1_wght => /=.
- by move=> u; rewrite ge0_mu1 le1_mu1.
rewrite sum0_eq => /= [u|].
- case: (u = f x0) => //= ne_u_fx0; rewrite mulf_eq0; right.
  rewrite dmap1E &(mu0_false) => g /dfun_supp /(_ x0).
  rewrite fupdate_eq supp_dunit /(\o) /pred1 => gx0E.
  by apply/negP => /fun_ext /(_ x0); rewrite fupdate_eq.
rewrite (@in_dmap1E_can _ _ (fun g => g.[x0 <- v])) /=.
- by apply/fun_ext=> x @/"_.[_<-_]"; case: (x0 = x).
- move=> g /dfun_supp /(_ x0) @{1}/"_.[_<-_]" /=.
  rewrite supp_dunit => gx0E <-; apply/fun_ext=> x.
  by rewrite /"_.[_<-_]"; case: (x0 = x).
rewrite dfun1E (@BRM.bigD1 _ _ x0) ?(FinT.enumP, FinT.enum_uniq) /=.
rewrite !fupdate_eq dunit1E /= -(@BRM.eq_bigr _ (fun x => mu1 (d x) (f x))) /=.
- by move=> x @/predC1 ne_x_x0; rewrite !fupdate_neq 1,2:eq_sym.
by rewrite (@BRM.bigD1 _ _ x0) ?(FinT.enumP, FinT.enum_uniq).
qed.

lemma dfunE_dlet_fix1 ['u] (d : t -> 'u distr) x0 :
  dfun d = dlet (d x0) (fun v => dfun d.[x0 <- dunit v]).
proof.
apply/eq_distr=> g; rewrite muE (@sum_partition (fun f => f x0)) /=.
- by apply/summable_mu1_cond.
rewrite dletE &(eq_sum) => u /=; rewrite (@sumE_fin _ [g]) //=.
- by move=> h; case: (u = h x0) => // _ @/pred1; case: (h = g).
rewrite BRA.big_seq1 {1}/pred1 /=; case: (u = g x0).
- by move=> ->; apply: dfun1E_fix1.
move=> ne_u_gx0; apply/eq_sym; rewrite mulf_eq0; right.
apply/supportPn; rewrite dfun_supp negb_forall; exists x0 => /=.
by rewrite fupdate_eq supp_dunit eq_sym.
qed.

lemma dlet_dfun_update ['u] (d : t -> 'u distr) x0 :
  dlet
    (dfun d)
    (fun f => dmap (d x0) (fun y => f.[x0 <- y]))
  = weight (d x0) \cdot dfun d.
proof.
rewrite {1}(@dfunE_dlet_fix1 _ x0) dlet_dlet.
rewrite (@eq_dlet _ (fun _ => dfun d) _ (d x0)) //=.
- by apply/dlet_dfun_fupdate_ll.
- by apply/dlet_cst_weight.
qed.

lemma dfun_projE ['u] (df : t -> 'u distr)  x :
    dmap (dfun df) (fun f => f x)
  = (weight (dfun df) / weight (df x)) \cdot df x.
proof.
apply: eq_distr=> y; rewrite dscalar1E.
- rewrite divr_ge0 ?ge0_weight /=; have := ge0_weight (df x).
  case/ler_eqVlt => [<-//|nz_dfx].
  by rewrite ler_pdivr_mulr // mulVf // gtr_eqF.
pose c := _ / _; rewrite dmap1E /(\o) {1}/pred1.
pose p x' y' := x <> x' \/ y = y'.
rewrite -(@mu_eq _ (fun f => forall x, p x (f x))).
- move=> f @/p /=; apply: eq_iff; split; first by move/(_ x) => /= <-.
  by move=> /eq_sym yE x'; case: (x = x').
rewrite dfunE (@BRM.bigD1 _ _ x) ?(FinT.enumP, FinT.enum_uniq) /=.
rewrite mulrC; case/ler_eqVlt: (ge0_weight (df x)).
- by move/eq_sym/weight_eq0_dnull => ->; rewrite !dnullE.
move=> dfx_gt0; congr; last first.
- by apply: mu_eq => @/p @/pred1 z /=; rewrite [z = y]eq_sym.
apply/eq_sym=> @/c; rewrite weight_dfun.
rewrite (@BRM.bigD1 _ _ x) ?(FinT.enumP, FinT.enum_uniq) /=.
rewrite mulrAC divff 1:gtr_eqF //=; apply: BRM.eq_bigr.
move=> x' @/predC1 ne_x /=; apply: mu_eq => @/predT.
by move=> y' @/p /=; rewrite [x = x']eq_sym ne_x.
qed.

lemma eq_from_dfun_proj_eq ['u] (df1 df2 : t -> 'u distr) :
     (forall x, is_lossless (df1 x))
  => (forall x, is_lossless (df2 x))
  => (forall x,
         dmap (dfun df1) (fun f => f x)
       = dmap (dfun df2) (fun f => f x))
  => df1 == df2.
proof.
move=> ll1 ll2 eq x; apply/eq_distr=> y.
have := eq x; rewrite !dfun_projE.
by rewrite !dfun_ll // !(ll1, ll2) /= !dscalar1 => ->.
qed.

lemma dfun_prod1E ['u 'v] (df : t -> 'u distr) (dg : t -> 'v distr) f g :
    mu1 (dfun (fun x => df x `*` dg x)) (fun x => (f x, g x))
  = mu1 (dfun df) f * mu1 (dfun dg) g.
proof.
pose F x := mu1 (df x) (f x) * mu1 (dg x) (g x).
rewrite dfun1E /= -(@BRM.eq_bigr _ F) //= /F => {F}.
- by move=> x _; rewrite dprod1E.
- by rewrite BRM.big_split -!dfun1E.
qed.

lemma dprod_funE ['u 'v] (df : t -> 'u distr) (dg : t -> 'v distr) :
  dfun df `*` dfun dg =
    dmap
      (dfun (fun x => df x `*` dg x))
      (fun fg => (fst \o fg, snd \o fg)).
proof.
apply/eq_distr; case=> f g; rewrite dprod1E dmap1E /(\o) /=.
pose E := pred1 (fun x : t => (f x, g x)).
rewrite -(@mu_eq _ E) /E 1:/pred1 => [h /=|].
- apply/eq_iff; split=> [->|[<- <-]] //=.
  by apply/fun_ext=> x; case: (h x).
- by rewrite dfun_prod1E.
qed.

lemma dfun_prodE ['u 'v] (df : t -> 'u distr) (dg : t -> 'v distr):
    dfun (fun x => df x `*` dg x)
  = dmap
      (dfun df `*` dfun dg)
      (fun fg : _ * _ => fun x => (fg.`1 x, fg.`2 x)).
proof.
pose F (fg : (t -> 'u) * (t -> 'v)) x := (fg.`1 x, fg.`2 x).
have /(congr1 (dapply F)) /= -> := dprod_funE df dg.
rewrite dmap_comp dmap_id_eq_in // /(\o) /F /=.
by move=> h _; apply/fun_ext=> x; case: (h x).
qed.

lemma dfun_condE ['u] (X : t -> bool) (dt df : t -> 'u distr) :
     (forall x, is_lossless (dt x))
  => (forall x, is_lossless (df x))
  =>
       dmap
         (dfun dt `*` dfun df)
         (fun tf : _ * _ => fun x => if X x then tf.`1 x else tf.`2 x)
     = dfun (fun x => if X x then dt x else df x).
proof.
move=> llt llf; rewrite dprod_funE dmap_comp /(\o) /=.
apply/eq_distr => f; rewrite dmap1E {1}/pred1 /(\o) /=.
pose p x (y : _ * _) := (if X x then y.`1 else y.`2) = f x.
rewrite -(@mu_eq _ (fun g : _ -> _ * _ => forall x, p x (g x))).
- by move=> h; rewrite fun_ext.
rewrite dfunE dfun1E /= !(@BRM.bigID predT _ X) !predTI; congr.
- apply: BRM.eq_bigr => x @/p /= -> /=.
  by rewrite (@dprodE (fun y => y = f x) predT) llf /=.
- apply: BRM.eq_bigr => x @/p /= -> /=.
  by rewrite (@dprodE predT (fun y => y = f x)) llt /=.
qed.

lemma dlet_dfun_cond ['u] (dX : t -> bool distr) (dt df : t -> 'u distr) :
     (forall x, is_lossless (dX x))
  => (forall x, is_lossless (dt x))
  => (forall x, is_lossless (df x))
  =>   dlet (dfun dX) (fun X => dfun (fun x => if X x then dt x else df x))
     = dfun (fun x => dlet (dX x) (fun b => if b then dt x else df x)).
proof.
move=> llX llt llf; apply/eq_distr=> f; apply/eq_sym.
pose p (x : t) :=
     mu1 (dX x) true  * mu1 (dt x) (f x)
   + mu1 (dX x) false * mu1 (df x) (f x).
rewrite dfun1E /= -(@BRM.eq_bigr _ p) //=.
- by move=> x _; rewrite dletE_bool.
rewrite dlet1E prodrDl2; first by apply: FinT.is_finite_for.
apply: eq_sum => X /=; rewrite !dfun1E -BRM.big_split /=.
by apply: BRM.eq_bigr => /= x _; case: (X x).
qed.

lemma dfun_dcondE ['u] (dX : t -> bool distr) (dt df : t -> 'u distr) :
     (forall x, is_lossless (dX x))
  => (forall x, is_lossless (dt x))
  => (forall x, is_lossless (df x))
  => 
       dlet (dfun dX) (fun X : t -> bool =>
         dmap
           (dfun dt `*` dfun df)
           (fun tf : _ * _ => (fun x => if X x then tf.`1 x else tf.`2 x)))
     = dfun (fun x => (mu1 (dX x) true \cdot dt x) + (mu1 (dX x) false \cdot df x)).
proof.
pose D X := dfun (fun x => if X x then dt x else df x).
move=> llX llt llf; rewrite -(@eq_dlet D _ (dfun dX)) //.
- by move=> X; apply/eq_sym/dfun_condE.
rewrite dlet_dfun_cond //; congr; apply/fun_ext => x /=.
apply/eq_distr=> u; rewrite dletE_bool /= dadd1E -1:!dscalar1E //.
- rewrite !weight_dscalar // ?(llt, llf) /= ?le1_mu.
  by rewrite -mu_disjoint ?le1_mu //; case.
- by rewrite ge0_mu1 /= llt /= le1_mu1.
- by rewrite ge0_mu1 /= llf /= le1_mu1.
qed.

end MUniFinFun.

abstract theory Dfun_sub.

type A, C.

clone MUniFinFun as MA with type t <- A.
clone MUniFinFun as MC with type t <- C.

section.
declare type B.
declare op dA : A -> B distr.

declare op p : A -> bool.
declare op g  : A -> C.
declare op gI : C -> A.

declare axiom g_inv : forall a, p a => gI (g a) = a.
declare axiom gI_inv : forall c, (g (gI c)) = c.

declare axiom pgI : forall c, p (gI c).

import StdBigop.Bigreal.BRM. 

lemma dfun_extend : 
  (forall a, !p a => is_lossless (dA a)) => 
  MC.dfun (fun c => dA (gI c)) = dmap (MA.dfun dA) (fun (f:A -> B) (c:C) => f (gI c)).
proof.
move=> dA_ll; pose dab := MA.dfun dA; pose dcb := MC.dfun (fun c => dA (gI c)).
apply/eq_distr => f.
have h := perm_filterC p MA.FinT.enum.
rewrite dmap1E /(\o) /pred1 /=.
pose P (a:A) (b : B) := p a => b = f (g a).
pose d := mu dab _.
have -> {d}: d = mu dab (fun fa => forall x, P x (fa x)).
+ apply mu_eq => fa /=.
  rewrite fun_ext /(==) /P. smt(g_inv gI_inv pgI).
rewrite MA.dfunE -(eq_big_perm h) big_cat.
have -> /= : BRM.big predT (fun (x : A) => mu (dA x) (P x)) (filter (predC p) MA.FinT.enum) = 1%r.
+ rewrite big_filter big1 //= /P  => a ha.
  rewrite -(dA_ll ha); apply mu_eq => /#.
rewrite MC.dfun1E.
have : perm_eq MC.FinT.enum (map g (filter p MA.FinT.enum)).
- apply/uniq_perm_eq.
  - by apply: MC.FinT.enum_uniq.
  - apply/map_inj_in_uniq; last first.
    - by apply/filter_uniq/MA.FinT.enum_uniq.
    move=> a1 a2 /mem_filter [ha1 _] /mem_filter [ha2 _].
    smt(g_inv gI_inv pgI).
  - move=> c; rewrite MC.FinT.enumP /=; apply/mapP.
    exists (gI c); rewrite mem_filter MA.FinT.enumP /=.
    smt(g_inv gI_inv pgI).
move/eq_big_perm => ->; rewrite big_map.
rewrite !big_filter; apply: eq_bigr => a ha.
by rewrite /(\o) /P /= g_inv ha.
qed.

lemma dfun_extend_if : 
 (forall a, is_lossless (dA a)) => 
  MA.dfun dA = 
   dmap (MA.dfun dA `*` MC.dfun (fun c => dA (gI c))) 
     (fun (f : _ * _) (x : A) => if p x then f.`2 (g x) else f.`1 x).
proof.
move=> dA_ll; rewrite dfun_extend; 1: by move=> *;apply dA_ll.
rewrite dmap_dprodR dmap_comp /(\o) /=.
have {1}-> : dA = fun x => if p x then dA x else dA x by done.
rewrite -MA.dfun_condE; 1,2: by apply dA_ll.
rewrite {1}dprodC dmap_comp /(\o); apply eq_dmap; smt(g_inv).
qed.

end section.

end Dfun_sub.

(* -------------------------------------------------------------------- *)
op mbin (p : real) (n : int) = fun k =>
  (bin n k)%r * (p ^ k * (1%r - p) ^ (n - k)).

lemma mbin_support p n k : mbin p n k <> 0%r => 0 <= k <= n.
proof.
apply: contraR; rewrite andaE negb_and -!ltrNge.
by case=> ? @/mbin; [rewrite bin_lt0r | rewrite bin_gt].
qed.

lemma isdistr_mbin p n : 0%r <= p <= 1%r => isdistr (mbin p n).
proof.
move=> rg_p; rewrite (@isdistr_finP (range 0 (n+1))).
+ apply: range_uniq.
+ by move=> k /mbin_support; rewrite mem_range ltzS.
+ move=> k @/mbin; rewrite mulr_ge0.
  * by rewrite le_fromint ge0_bin.
  by rewrite mulr_ge0 expr_ge0 /#.
case: (n < 0) => [lt0_n|/lezNgt ge0_n]; first by rewrite big_geq //#.
by rewrite -(@BCR.binomial p (1%r - p) n ge0_n) addrC subrK expr1z.
qed.

op dbin (p : real) (n : int) = mk (mbin p n).

lemma dbin1E (p : real) (n k : int) : 0%r <= p <= 1%r =>
  mu1 (dbin p n) k = (bin n k)%r * (p ^ k * (1%r - p) ^ (n - k)).
proof. by move=> rg_p; rewrite muK //; apply/isdistr_mbin. qed.

lemma ll_dbin p n : 0 <= n => 0%r <= p <= 1%r => is_lossless (dbin p n).
proof.
move=> ge0_n rg_p; rewrite /is_lossless weightE /dbin muK' 1:&(isdistr_mbin) //.
rewrite (@sumE_fin _ (range 0 (n+1))) 1:range_uniq.
+ by move=> k /mbin_support; rewrite mem_range ltzS.
+ by rewrite -BCR.binomial // addrC subrK expr1z.
qed.

lemma supp_dbin p n k : 0%r <= p <= 1%r => k \in dbin p n => 0 <= k <= n.
proof.
by move=> rg_p /supportP; rewrite dbin1E // => /mbin_support.
qed.

(* -------------------------------------------------------------------- *)
op mdlim (df : int -> 'a distr) =
  fun x => lim (fun n => mass (df n) x).

lemma isdistr_dlim (df : int -> 'a distr) : isdistr (mdlim df).
proof.
pose F x := fun n : int => mass (df n) x.
split=> @/mdlim /= [x|s uq_s].
- case: (converge (F x))%RealSeq => [|/lim_Ncnv ->//].
  apply: (geC_lim_from 0) => n _.
  by rewrite /s /F massE ge0_mu1.
rewrite (@bigID _ _ (fun x => RealSeq.converge (F x))).
rewrite addrC big1 -1:add0r.
- by move=> x [_ @/predC] /lim_Ncnv /=; apply.
rewrite predTI -big_filter; pose t := filter _ _.
have: uniq t by rewrite filter_uniq.
have: forall x, x \in t => RealSeq.converge (F x).
- by move=> x; rewrite mem_filter.
move: t => {s uq_s} s cvg_s uq_s.
rewrite big_seq lim_sum // &(leC_lim_from 0) /=.
- move=> n _ /=; rewrite -(@big_seq _ s).
  apply: le1_sum_isdistr => //.
  rewrite -(@eq_isdistr (mu1 (df n))) /=.
  - by move=> x /=; rewrite massE.
  - by apply: isdistr_mu1.
- by apply: converge_sum => x x_s /=; apply: cvg_s.
qed.

(* -------------------------------------------------------------------- *)
op E ['a] (d : 'a distr) (f : 'a -> real) =
  sum (fun x => f x * mu1 d x).

op Ec ['a] (d : 'a distr) (f : 'a -> real) (p : 'a -> bool) =
  E d (fun x => if p x then f x else 0%r) / mu d p.

(* -------------------------------------------------------------------- *)
pred hasE (d : 'a distr) (f : 'a -> real) =
  summable (fun x => f x * mu1 d x).

(* -------------------------------------------------------------------- *)
lemma hasE_finite ['a] (d : 'a distr) f :
  is_finite (support d) => hasE d f.
proof.
move=> fin_d; apply/(@summable_fin _ (to_seq (support d))) => /=.
move=> a; apply: contraR; rewrite mem_to_seq //.
by move/supportPn => ->.
qed.

(* -------------------------------------------------------------------- *)
lemma hasE_uniform ['a] (d : 'a distr) f :
  is_uniform d => hasE d f.
proof. by move=> uf_d; apply/hasE_finite/uniform_finite. qed.

(* -------------------------------------------------------------------- *)
lemma eq_hasE ['a] d f g: f == g => hasE<:'a> d f <=> hasE<:'a> d g.
proof. by move=> eq_fg; apply: eq_summable=> /= a; rewrite eq_fg. qed.

(* -------------------------------------------------------------------- *)
lemma hasE_cond ['a] d f p :
  hasE<:'a> d f => hasE d (fun x => if p x then f x else 0%r).
proof.
pose F := fun x => if p x then f x * mu1 d x else 0%r.
move=> Edf @/hasE; rewrite -(@eq_summable F) /=.
- by move=> x @/F; case: (p x).
- by apply: summable_cond.
qed.

lemma hasE_dcond (d : 'a distr) (p : 'a -> bool) (f : 'a -> real) :
  hasE d f => hasE (dcond d p) f.
proof.
rewrite /hasE => Edf.
apply (@summable_le (fun x => inv (mu d p) * (f x * mu1 d x))) => [|x /=].
- exact/summableZ.
- by rewrite dcond1E; case: (p x)=> /#.
qed.

(* -------------------------------------------------------------------- *)
lemma eq_expL ['a] (d1 d2 : 'a distr) f : d1 = d2 => E d1 f = E d2 f.
proof. by move=> ->. qed.

(* -------------------------------------------------------------------- *)
lemma eq_exp (d : 'a distr) (f g : 'a -> real) :
     (forall x, x \in d => f x = g x)
  => E d f = E d g.
proof.
move=> eq_fg; apply/eq_sum => x /=; case: (mu1 d x = 0%r) => [->//|].
by move/supportP /eq_fg => ->.
qed.

(* -------------------------------------------------------------------- *)
lemma hasE_le (d : 'a distr) (f g : 'a -> real) :
     hasE d g
  => (forall x, `|f x| <= `|g x|)
  => hasE d f.
proof.
move=> heg le_fg; apply/(summable_le _ heg) => /=.
by move=> x; rewrite !normrM ler_wpmul2r 1:normr_ge0 le_fg.
qed.

(* -------------------------------------------------------------------- *)
lemma hasE_pos ['a] d f : hasE<:'a> d f => hasE<:'a> d (pos f).
proof.
move/summable_le; apply=> /= a; rewrite !normrM ler_wpmul2r.
- by apply normr_ge0. - by apply: abs_pos_ler.
qed.

(* -------------------------------------------------------------------- *)
lemma hasE_neg ['a] d f : hasE<:'a> d f => hasE<:'a> d (neg f).
proof.
move/summable_le; apply=> /= a; rewrite !normrM ler_wpmul2r.
- by apply normr_ge0. - by apply: abs_neg_ler.
qed.

(* -------------------------------------------------------------------- *)
lemma hasEC (d : 'a distr) (c : real) : hasE d (fun _ => c).
proof.
exists `|c| => J uqJ; pose f := fun i => `|c| * mu1 d i.
rewrite -(@eq_bigr _ f) /= => [i _|].
+ by rewrite normrM (@ger0_norm (mu1 _ _)).
rewrite /f -mulr_sumr ler_pimulr 1:normr_ge0.
by apply/(@le1_mu1_fin d).
qed.

(* -------------------------------------------------------------------- *)
lemma hasEN ['a] d f : hasE<:'a> d (fun x => -f x)%Real <=> hasE d f.
proof. by apply: eq_summable_norm => /= a; rewrite !normrM normrN. qed.

(* -------------------------------------------------------------------- *)
lemma hasEZ ['a] d f c : hasE<:'a> d f => hasE d (fun x => c * f x).
proof.
rewrite /hasE => /(@summableZ _ c); apply: eq_summable => /=.
by move=> a; rewrite !mulrA.
qed.

(* -------------------------------------------------------------------- *)
lemma hasEZr ['a] d f c : hasE<:'a> d f => hasE d (fun x => f x * c).
proof.
by move/(@hasEZ _ _ c); apply: eq_summable=> /= a; rewrite (@mulrC _ c).
qed.

(* -------------------------------------------------------------------- *)
lemma summable_hasE (d : 'a distr) (f : 'a -> real) :
  summable f => hasE d f.
proof.
move=> sbl_f; apply/(@summable_le f) => //= x.
by rewrite normrM ler_pimulr ?normr_ge0 ger0_norm.
qed.

(* -------------------------------------------------------------------- *)
lemma exp_eq0 ['a] (d : 'a distr) f :
  (forall x, x \in d => f x = 0%r) => E d f = 0%r.
proof.
move=> z_f; rewrite /E sum0_eq //= => a.
by case: (mu1 d a = 0%r) => [->//|]; move/supportP => /z_f ->.
qed.

(* -------------------------------------------------------------------- *)
lemma exp_cond_eq0 ['a] (d : 'a distr) f p :
  (forall x, x \in d => p x => f x = 0%r) => Ec d f p = 0%r.
proof. by move=> z_f; rewrite /Ec exp_eq0 //#. qed.

(* -------------------------------------------------------------------- *)
lemma exp_ge0 ['a] (d : 'a distr) f :
  (forall x, x \in d => 0%r <= f x) => 0%r <= E d f.
proof.
move=> ge0_f; apply: ge0_sum => a /=.
by case: (mu1 d a = 0%r) => [->//|^/supportP /ge0_f]; smt(ge0_mu).
qed.

(* -------------------------------------------------------------------- *)
lemma exp_cond_ge0 ['a] (d : 'a distr) f p :
  (forall x, x \in d => p x => 0%r <= f x) => 0%r <= Ec d f p.
proof.
move=> ge0_f; rewrite /Ec mulr_ge0; last first.
- by apply/invr_ge0/ge0_mu. - by apply: exp_ge0 => /#.
qed.

(* -------------------------------------------------------------------- *)
lemma expC_cond (d : 'a distr) (c : real) (P : 'a -> bool) :
  E d (fun x => if P x then c else 0%r) = c * mu d P.
proof.
by rewrite /E muE -sumZ; apply/eq_sum => x /=; rewrite !fun_if2.
qed.

(* -------------------------------------------------------------------- *)
lemma expC (d : 'a distr) (c : real) :
  E d (fun _ => c) = c * weight d.
proof. by rewrite /E sumZ -weightE. qed.

(* -------------------------------------------------------------------- *)
lemma expC_prod ['a 'b] (d1 : 'a distr) (d2 : 'b distr) c :
  E d1 (fun _ => E d2 (fun _ => c)) = E (d1 `*` d2) (fun _ => c).
proof. by rewrite !expC weight_dprod #ring. qed.

(* -------------------------------------------------------------------- *)
lemma expD (d : 'a distr) f1 f2 :
     hasE d f1 => hasE d f2
  => E d (fun x => f1 x + f2 x) = E d f1 + E d f2.
proof.
move=> h1 h2; pose f := fun x => f1 x * mu1 d x + f2 x * mu1 d x.
by rewrite /E -(@eq_sum f) /f 1?sumD //= => x; rewrite mulrDl.
qed.

(* -------------------------------------------------------------------- *)
lemma expD_cond ['a] (d : 'a distr) (f g : 'a -> real) p :
     hasE d (fun x => if p x then f x else 0%r)
  => hasE d (fun x => if p x then g x else 0%r)
  => Ec d (fun x => f x + g x) p = Ec d f p + Ec d g p.
proof.
move=> Edf Edg; rewrite /Ec -mulrDl; congr; rewrite -expD 1,2://.
by apply: eq_sum=> /= x; case: (p x).
qed.

(* -------------------------------------------------------------------- *)
lemma expN ['a] d f : E<:'a> d (fun x => -(f x))%Real = - E d f.
proof.
rewrite /E -(@eq_sum (fun x => - (f x * mu1 d x))) /=.
+ by move=> a; rewrite mulNr.
+ by rewrite sumN.
qed.

(* -------------------------------------------------------------------- *)
lemma expB ['a] d f g : hasE d f => hasE d g =>
  E<:'a> d (fun x => f x - g x) = E d f - E d g.
proof. by move=> Edf Edg; rewrite expD 1?hasEN 1,2:// expN. qed.

(* -------------------------------------------------------------------- *)
lemma expZ ['a] d (c : real) f : E<:'a> d (fun x => c * f x) = c * E d f.
proof. by rewrite /E -sumZ &(eq_sum) => /= a; rewrite mulrA. qed.

(* -------------------------------------------------------------------- *)
lemma exp_norm ['a] d f : hasE<:'a> d f => `|E d f| <= E d (fun x => `|f x|).
proof.
move=> Edf; rewrite -(@eq_exp _ (fun x => pos f x - neg f x)) /=.
- by move=> a ad; apply/eq_sym/pos_neg_id.
rewrite expB; 1,2: by rewrite 1?(hasE_pos, hasE_neg).
have /ler_trans := ler_norm_sub (E d (pos f)) (E d (neg f)); apply.
rewrite !ger0_norm.
- by apply: ge0_sum=> /= a; rewrite mulr_ge0 // pos_ge0.
- by apply: ge0_sum=> /= a; rewrite mulr_ge0 // neg_ge0.
rewrite -expD; 1,2: by rewrite 1?(hasE_pos, hasE_neg).
by apply/lerr_eq/eq_exp=> /= a _; rewrite pos_neg_abs.
qed.

(* -------------------------------------------------------------------- *)
lemma exp_dnull ['a] f : E dnull<:'a> f = 0%r.
proof. by rewrite /E sum0_eq //= => a; rewrite dnull1E. qed.

(* -------------------------------------------------------------------- *)
lemma exp_dunit ['a] x f : E<:'a> (dunit x) f = f x.
proof.
rewrite /E (@sumE_fin _ [x]) //=.
+ move=> a; rewrite mulf_eq0 negb_or => -[_].
  by move/supportP; rewrite supp_dunit.
+ by rewrite BRA.big_seq1 /=; rewrite dunit1E.
qed.

(* -------------------------------------------------------------------- *)
lemma hasE_drestrict ['a] d p f : hasE d f => hasE (drestrict<:'a> d p) f.
proof.
move/summable_le; apply=> /= a; rewrite !normrM ler_wpmul2l 1:normr_ge0.
rewrite drestrict1E; case: (p a) => // _.
by rewrite normr0 normr_ge0.
qed.

(* -------------------------------------------------------------------- *)
lemma exp_cond_drestrict_le ['a] d (p q : _ -> bool) f :
  q <= p => Ec (drestrict<:'a> d p) f q = Ec d f q.
proof.
move=> le_qp; rewrite /Ec drestrictE_le ~-1://; congr.
by apply: eq_sum=> /= a; rewrite drestrict1E /#.
qed.

(* -------------------------------------------------------------------- *)
lemma exp_cond_dunit ['a] (x : 'a) f p :
  Ec (dunit x) f p = if p x then f x else 0%r.
proof.
rewrite /Ec exp_dunit /=; case: (p x) => //.
by rewrite dunitE => ->.
qed.

(* -------------------------------------------------------------------- *)
lemma exp_drestrict ['a] d p f :
  E (drestrict<:'a> d p) f = mu d p * Ec d f p.
proof.
have /ler_eqVlt[^ + <- /=|nz_mudp] := ge0_mu d p; last first.
- rewrite /Ec mulrCA divff /=; first by rewrite gtr_eqF.
  by apply: eq_sum=> /= a; rewrite drestrict1E; case: (p a).
- move/eq_sym/eq0_mu => Np; apply: sum0_eq => /= a.
  rewrite drestrict1E; case: (p a) => //; apply: contraLR.
  by rewrite mulf_eq0 negb_or -supportP /#.
qed.

(* -------------------------------------------------------------------- *)
lemma exp_duniform ['a] (s : 'a list) f :
  E (duniform s) f = (1%r / (size (undup s))%r) * BRA.big predT f (undup s).
proof.
rewrite /E (@sumE_fin _ (undup s)) 1:undup_uniq /=.
- move=> a; rewrite mulf_eq0 negb_or; case=> _.
  by move/supportP; rewrite supp_duniform mem_undup.
- rewrite BRA.mulr_suml !BRA.big_seq &(BRA.eq_bigr) => /= a.
  by rewrite mem_undup => a_in_s; rewrite  duniform1E a_in_s.
qed.

(* -------------------------------------------------------------------- *)
lemma exp_dlet ['a 'b] (d : _ distr) (df : 'a -> 'b distr) f :
  hasE (dlet d df) f => E (dlet d df) f = E d (fun x => E (df x) f).
proof.
move=>h; pose s (a : 'a) (b : 'b) := f b * mu1 (df a) b * mu1 d a.
rewrite /E -(@eq_sum (fun a => sum (s a))) /=; 1: by move=> a; rewrite sumZr.
rewrite (@sum_swap (fun ab : _ * _ => s ab.`1 ab.`2)).
- exists (psum (fun x => f x * mu1 (dlet d df) x)).
  move=> J uqJ; pose K := undup (unzip2 J).
  have uqK: uniq K by apply: undup_uniq.
  have le := ler_big_psum (fun x => f x * mu1 (dlet d df) x) K h uqK.
  apply: (ler_trans _ _ le) => {le}.
  rewrite BRA.big_pair_pswap /= {1}/pswap /(\o) /= BRA.big_pair.
  - by apply/map_inj_in_uniq=> //=; first case=> [??] [??] _ _[].
  have: (perm_eq (undup (unzip1 (map pswap J))) K).
  - apply: uniq_perm_eq; 1,2: by apply/undup_uniq.
    by move=> x @/K; rewrite !mem_undup -map_comp -(@eq_map snd).
  move/BRA.eq_big_perm=> ->; apply: Bigreal.ler_sum => /=.
  move=> b _ @/s => {s}; pose s a := `|f b| * (mu1 (df a) b * mu1 d a).
  rewrite BRA.big_filter -(@BRA.eq_bigr _ (fun ba : _ * _ => s ba.`2)) /=.
  - case=> b' a' /= ->> @/pswap /= @/s.
    by rewrite -!mulrA !normrM; congr; rewrite !ger0_norm.
  rewrite {1}/pswap /s /= -BRA.mulr_sumr normrM.
  rewrite ler_wpmul2l 1:normr_ge0 BRA.big_map /(\o) /= -BRA.big_filter.
  rewrite ger0_norm //; pose L := List.filter _ _.
  rewrite (@BRA.sum_pair (fun x => mu1 (df x) b * mu1 d x) (fun _ => 1%r)) /=.
  - by apply: filter_uniq.
  move=> {s}; pose s a := mu1 (df a) b * mu1 d a.
  apply: (@ler_trans (BRA.big predT s (undup (unzip1 L)))).
  - apply: Bigreal.ler_sum=> a _ @/s /=; apply: ler_pimulr.
    - by rewrite mulr_ge0.
    pose M := List.filter _ _; have memM: (mem M) <= (mem [(a, b)]).
    - by case=> a' b'; rewrite !mem_filter /=.
    have: uniq M by do 2! apply/filter_uniq.
    move/uniq_leq_size=> /(_ _ memM) /= szM.
    by rewrite Bigreal.sumr1 size_map le_fromint.
  have := undup_uniq (unzip1 L); move: (undup _) => {J uqJ K uqK L} J uqJ.
  have sm_s: summable s.
  - apply: (@eq_summable (fun a => mu1 d a * mu1 (df a) b)).
    - by move=> a /=; rewrite mulrC.
    by apply/summable_mu1_wght => a /=; rewrite ge0_mu1.
  rewrite dlet1E -sum_norm /=; first by move=> a; rewrite mulr_ge0.
  rewrite -psum_sum; 1: by apply: eq_summable sm_s => /= a; rewrite /s mulrC.
  apply: (ler_trans _ _ (ler_big_psum _ uqJ)) => //=; last first.
  - by apply: eq_summable sm_s => /= a @/s; rewrite mulrC.
  apply/lerr_eq/BRA.eq_bigr=> /= a _ @/s.
  by rewrite normrM !ger0_norm // mulrC.
apply: eq_sum=> /= b @/s; rewrite dlet1E -sumZ /=.
by apply: eq_sum=> /= a; rewrite mulrAC mulrA.
qed.

(* -------------------------------------------------------------------- *)
lemma exp_cond_dlet ['a 'b] d df f p: hasE (dlet d df) f =>
    Ec (dlet<:'a, 'b> d df) f p
  = E d (fun x => (mu (df x) p / mu (dlet d df) p * Ec (df x) f p)).
proof.
move=> Edf; rewrite /Ec exp_dlet; first by apply: hasE_cond.
rewrite mulrC -expZ &(eq_exp) => /= a a_in_d.
rewrite mulrC -2!expZ mulrC -expZ /=.
apply: eq_exp => /= b b_in_dfa; case: (p b) => // pb.
have nz1: mu (df a) p <> 0%r by apply/negP=> /eq0_mu /(_ b b_in_dfa).
have nz2: mu (dlet d df) p <> 0%r.
- apply/negP=> /eq0_mu /(_ b); apply=> //.
  by rewrite supp_dlet; exists a.
by field=> //; rewrite mulf_eq0 negb_or.
qed.

(* -------------------------------------------------------------------- *)
lemma exp_dmap ['a 'b] d (f : 'a -> 'b) (g : 'b -> real) : hasE (dmap d f) g =>
  E (dmap d f) g = E d (g \o f).
proof.
move=> Edf; rewrite exp_dlet -/(dmap _ _) 1://.
by apply: eq_exp=> a _ /=; rewrite exp_dunit.
qed.

(* TOTHINK: should this be the defintion of Ec *)
lemma exp_dcond (d : 'a distr) (p : 'a -> bool) (f : 'a -> real) :
  E (dcond d p) f = Ec d f p.
proof.
by rewrite /Ec /E -sumZr &(eq_sum) /= => x; rewrite dcond1E /#.
qed.

(* -------------------------------------------------------------------- *)
lemma in_ler_exp ['a] (d : 'a distr) (f g : 'a -> real) :
     hasE d f => hasE d g
  => (forall (x : 'a), x \in d => f x <= g x)
  => E d f <= E d g.
proof.
move=> Edf Edg le_fg; apply: RealSeries.ler_sum => //= x.
case: (mu1 d x = 0%r) => [->//|/supportP].
by move/le_fg => le_fg_x; apply: ler_wpmul2r.
qed.

(* -------------------------------------------------------------------- *)
lemma in_ler_exp_cond ['a] (d : 'a distr) (f g : 'a -> real) p :
     hasE d f => hasE d g
  => (forall (x : 'a), x \in d => p x =>f x <= g x)
  => Ec d f p <= Ec d g p.
proof.
move=> Edf Edg le_fg @/Ec; apply: ler_wpmul2r; first by rewrite invr_ge0.
apply: in_ler_exp => /=; 1,2: by apply: hasE_cond.
by move=> x xd; case: (p x) => //; apply: le_fg.
qed.

(* -------------------------------------------------------------------- *)
lemma ler_exp (d : 'a distr) (f g : 'a -> real) :
     hasE d f => hasE d g
  => (forall x, f x <= g x)
  => E d f <= E d g.
proof. by move=> ?? le; apply: in_ler_exp => // ? _; apply: le. qed.

(* -------------------------------------------------------------------- *)
lemma ler_exp_pos (d : 'a distr) (f g : 'a -> real) :
     hasE d g
  => (forall x, 0%r <= f x <= g x)
  => E d f <= E d g.
proof.
move=> hef le_fg; apply/ler_exp => //.
+ by apply/(hasE_le _ hef) => x /#.
+ by move=> x; case: (le_fg x).
qed.

(* -------------------------------------------------------------------- *)
lemma iscpl_hasEL ['a 'b] da db d f :
  iscoupling<:'a, 'b> da db d => hasE da f => hasE d (f \o fst).
proof.
move=> iscpl [M sM]; exists M => J uqJ.
rewrite BRA.big_pair //=; pose K := undup (unzip1 J).
(have /sM: uniq K by apply: undup_uniq); apply/(ler_trans _).
apply: Bigreal.ler_sum => a _ /=; rewrite BRA.big_seq.
rewrite -(@BRA.eq_bigr _ (fun i : _ * _ => `|f a| * mu1 d i)) /=.
  case=> a' b'; rewrite mem_filter /= => -[<- _].
  by rewrite normrM; congr => //; rewrite ger0_norm.
rewrite -BRA.mulr_sumr normrM ler_wpmul2l 1:normr_ge0.
pose s := List.filter _ J; rewrite -(@BRA.big_seq _ s).
rewrite BRA.big_filter BRA.big_mkcond /=.
apply: (@ler_trans (mu d (fun xy : _ * _ => xy.`1 = a))).
- rewrite muE /= (@sum_split _ (mem J)) /=.
    by apply/summable_cond/summable_mu1.
  apply: ler_paddr; first apply: ge0_sum => /=.
    by move=> x; case: (!_) => //=; case: (_ = _).
  rewrite (sumE_fin uqJ) /=; first by move=> x; case: (x \in J).
  rewrite -(@BRA.big_mkcond (mem J)) -(@BRA.big_filter (mem J)).
  by rewrite eq_in_filter_predT.
- by rewrite ger0_norm // (iscpl_muL _ iscpl).
qed.

(* -------------------------------------------------------------------- *)
lemma iscpl_hasER ['a 'b] da db d f :
  iscoupling<:'a, 'b> da db d => hasE db f => hasE d (f \o snd).
proof.
move=> + h - /iscpl_sym /iscpl_hasEL /(_ f h).
move/(summable_bij _ _ bij_pswap) => @/(\o) @/pswap /=.
move/eqL_summable; apply => /= x.
by congr; rewrite dmap1E; apply: mu_eq; case => /#.
qed.

(* -------------------------------------------------------------------- *)
lemma iscpl_E_split ['a 'b] da db f g d :
     iscoupling<:'a, 'b> da db d => hasE da f => hasE db g =>
  E da f + E db g = E d (fun xy : 'a * 'b => f xy.`1 + g xy.`2).
proof.
move=> hcpl daf dbg; rewrite expD.
- by apply/(iscpl_hasEL _ _ hcpl).
- by apply/(iscpl_hasER _ _ hcpl).
congr; rewrite /E.
- rewrite (@sum_partition fst) /=; first by apply/(iscpl_hasEL _ _ hcpl).
  apply: eq_sum => a /=; rewrite (iscpl_muL _ hcpl) muE mulrC -sumZr /=.
  apply: eq_sum => x /= @/(\o) @/pred1; rewrite (@eq_sym a).
  by case: (x.`1 = a) => // ->; rewrite mulrC.
- rewrite (@sum_partition snd) /=; first by apply/(iscpl_hasER _ _ hcpl).
  apply: eq_sum => b /=; rewrite (iscpl_muR _ hcpl) muE mulrC -sumZr /=.
  apply: eq_sum => x /= @/(\o) @/pred1; rewrite (@eq_sym b).
  by case: (x.`2 = b) => // ->; rewrite mulrC.
qed.

(* -------------------------------------------------------------------- *)
lemma E_split ['a] p f d : hasE<:'a> d f => E d f =
    E d (fun x => if  p x then f x else 0%r)
  + E d (fun x => if !p x then f x else 0%r).
proof.
move=> Efd @/E; rewrite (@sum_split _ p) 1:&(Efd).
by congr; apply/eq_sum => /= x; case: (p x).
qed.

(* -------------------------------------------------------------------- *)
lemma Ec_split ['a] p f d : hasE<:'a> d f =>
  E d f = mu d p * Ec d f p + mu d (predC p) * Ec d f (predC p).
proof.
move=> Edf; rewrite (@E_split p) //=; congr.
- rewrite /Ec mulrCA; case: (mu d p = 0%r) => mudp; last by rewrite divff.
  rewrite mudp /= -(@eq_exp _ (fun _ => 0%r)) ?expC //=.
  by move=> x xd; case: (p x) => //; have := eq0_mu _ _ mudp _ xd.
- rewrite /Ec mulrCA; case: (mu d (predC p) = 0%r) => mudp; last by rewrite divff.
  rewrite mudp /= -(@eq_exp _ (fun _ => 0%r)) ?expC //=.
  by move=> x xd; case: (p x) => //=; have @/predC := eq0_mu _ _ mudp _ xd.
qed.

(* -------------------------------------------------------------------- *)
op partition ['a] (d : 'a distr) p k =
     (forall i, mu d (p i) <> 0%r => 0 <= i < k)
  /\ (forall x, x \in d => exists i, 0 <= i < k /\ p i x)
  /\ (forall i j x, i <> j => !(p i x /\ p j x)).

lemma ptt_in_pred ['a] (d : 'a distr) p k :
  partition d p k => forall a, a \in d => exists i, 0 <= i < k /\ p i a.
proof. by case. qed.

lemma ppt_disjoint ['a] (d : 'a distr) p k :
  partition d p k => forall i j x, i <> j => !(p i x /\ p j x).
proof. by case. qed.

lemma partition_drestrict ['a] (d : 'a distr) p k : 0 <= k =>
  partition d p (k+1) => partition (drestrict d (predC (p k))) p k.
proof.
move=> ge0_k [h1 [h2 h3]]; do! split=> //.
- move=> i hpi; have ne_ik: i <> k.
  - by apply: contra hpi => ->; rewrite drestrictE predCI mu0.
  have := h1 i _; last by move=> /#.
  apply: contra hpi; rewrite drestrictE => /eq0_mu Npi.
  by apply: mu0_false => a /Npi @/predI ->.
- by move=> a; rewrite supp_drestrict /predC /= => -[] /h2[] /#.
qed.

(* -------------------------------------------------------------------- *)
lemma E_splits ['a] p f d k :
     hasE d f
  => partition d p k
  => E<:'a> d f = BRA.bigi predT (fun i => mu d (p i) * Ec d f (p i)) 0 k.
proof.
move=> Edf; elim/natind: k d Edf => [k le0_k|k ge0_k ih] d Edf hpdk.
- rewrite BRA.big_geq // (_ : d = dnull) -1:exp_dnull //.
  apply/eq_distr=> a; rewrite dnull1E; apply/supportPn.
  apply: contraL le0_k; rewrite lezNgt /=.
  by case/(ptt_in_pred _ _ _ hpdk) => /#.
rewrite (@Ec_split (p k)) ~-1:// BRA.big_int_recr ~-1:// /= addrC; congr.
pose dCp := drestrict d (predC (p k)); have := ih dCp _ _.
- by apply: hasE_drestrict.
- by apply: partition_drestrict.
rewrite exp_drestrict => ->; rewrite !BRA.big_seq &(BRA.eq_bigr) /=.
move=> i /mem_range rg_i; have dj_pi_Cpk: p i <= predC (p k).
- by move=> x @/predC /=; (have := ppt_disjoint _ _ _ hpdk i k x _) => /#.
by rewrite drestrictE_le 1:// exp_cond_drestrict_le.
qed.

(* -------------------------------------------------------------------- *)
lemma exp_cond_dlet_ilvt ['a] d df f p:
     hasE (dlet d df) f
  => hasE d (fun (x : 'a) => E (drestrict (df x) p) f)
  => (forall x, x \in d => !p x => mu (df x) p = 0%r)
  => (forall x, x \in d =>  p x => mu (df x) p = 1%r)
  =>   Ec (dlet<:'a, 'a> d df) f p
     = Ec d (fun x => E (df x) f) p.
proof.
move=> Edf Edf' h1 h2; rewrite exp_cond_dlet 1://.
rewrite (@E_split p) /=.
- apply: hasEZr; rewrite (@eq_hasE _ _ (fun x => E (drestrict (df x) p) f)) //=.
  by move=> a /=; rewrite exp_drestrict.
rewrite addrC (@eq_exp _ _ (fun _ => 0%r)) /=.
- by move=> a a_in_d; case: (p a) => //= /(h1 _ a_in_d) ->.
rewrite /E /Ec sum0_eq 1:// /= -sumZr &(eq_sum) => /= a.
case: (p a); last done.
move=> pa; case: (a \in d); last by move/supportPn=> ->.
move=> a_in_d; rewrite h2 1,2:// /=; do 2! congr; last first.
- move=> {a pa a_in_d}; rewrite dlet_muE_swap muE &(eq_sum) => /= a.
  pose F b := mu1 d a * (if p b then mu1 (df a) b else 0%r).
  rewrite -(@eq_sum F); first by move=> @/F /= x; case: (p x).
  rewrite /F sumZ -muE; case: (a \in d); last first.
  - by move/supportPn=> ->.
  move=> a_in_d; case: (p a) => pa.
  - by rewrite h2. - by rewrite h1.
rewrite /E &(eq_sum) => /= a'; case: (p a') => //=.
move=> Npa'; suff ->//: mu1 (df a) a' = 0%r; have := h2 _ a_in_d pa.
apply: contraLR => /supportP a'_dfa; rewrite eqr_le le1_mu /=.
have: mu (df a) (predU p (pred1 a')) <= 1%r by apply: le1_mu.
rewrite mu_disjointL 1:/# -ltrNge => le.
apply/(ltr_le_trans _ _ le)/ltr_addl; rewrite ltr_neqAle ge0_mu /=.
by rewrite eq_sym; apply/supportP.
qed.

(* -------------------------------------------------------------------- *)

lemma fin_expE (d : 'a distr) (f : 'a -> real) : is_finite (support d) =>
  E d f = big predT (fun x => f x * mu1 d x) (to_seq (support d)).
proof.
move => fin_d; rewrite /E (@sumE_fin _ (to_seq (support d))) ?uniq_to_seq //.
by move => x; rewrite mem_to_seq //; smt(supportP).
qed.

(* ==================================================================== *)
lemma Jensen_fin ['a] (d : 'a distr) f g :
     is_finite (support d)
  => is_lossless d
  => (forall a b, convex g a b)
  => g (E d f) <= E d (g \o f).
proof.
move=> fin_d ll_d cvx_g; rewrite !fin_expE /(\o) //; pose s := to_seq _.
move: ll_d; rewrite /is_lossless weightE !(@sumE_fin _ s) ?uniq_to_seq //=.
- by move=> a; rewrite -supportP mem_to_seq.
move=> {fin_d}; case: s => [|i s]; first by rewrite BRA.big_nil.
rewrite !BRA.big_consT /=.
elim: s (mu1 d i) (ge0_mu d (pred1 i)) (f i) => [|x s ih] l ge0_l v.
- by rewrite !BRA.big_nil /= => ->.
rewrite !BRA.big_consT /=; have := ge0_mu d (pred1 x).
rewrite ler_eqVlt => -[<-/=|gt0_dx]; first by apply: ih.
rewrite !addrA => eq1.
pose z := (v * l + f x * mu1 d x) / (l + mu1 d x).
have nz_dn: mu1 d x + l <> 0%r by rewrite gtr_eqF ?ltr_paddr.
have := ih _ _ z eq1; first by rewrite addr_ge0.
rewrite /z mulrVK 1:addrC // => /ler_trans; apply.
rewrite ler_add2r mulrDl -!mulrA; pose c1 := _ / _; pose c2 := _ / _.
have c2E: c2 = 1%r - c1; first by rewrite /c1 /c2 #field.
pose c := l + mu1 d x; pose t := g v * (c * c1) + g (f x) * (c * c2).
apply: (@ler_trans t); last by rewrite /t /c /c1 /c2 &(lerr_eq) #field.
rewrite /t !(@mulrC _ c1) !(@mulrC _ c2) !(@mulrC _ (_ * _)%Real).
rewrite !(@mulrAC _ c) -mulrDl ler_wpmul2r 1:addr_ge0 //.
rewrite c2E &(cvx_g) /c1 mulr_ge0 ?invr_ge0 // 1:addr_ge0 //=.
by rewrite ler_pdivr_mulr /= ?ler_addl // (ler_lt_trans _ ge0_l) ltr_addl.
qed.

lemma Jensen_fin_concave ['a] (d : 'a distr) f (g : real -> real) :
     is_finite (support d)
  => is_lossless d
  => (forall a b, convex (fun x => - g x) a b)
  => E d (g \o f) <= g (E d f).
proof.
move => d_fin d_ll g_concave.
have /= J := Jensen_fin d f (fun x => - g x) d_fin d_ll g_concave.
rewrite -ler_opp2; apply (@ler_trans _ _ _ J).
by rewrite -mulN1r -expZ lerr_eq &(eq_exp) => x x_d @/(\o) /=; rewrite mulN1r.
qed.
