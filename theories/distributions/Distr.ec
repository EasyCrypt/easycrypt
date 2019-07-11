(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

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
require import AllCore List.
require import Ring StdRing StdOrder StdBigop Discrete RealSeq RealSeries.
(*---*) import IterOp Bigint Bigreal Bigreal.BRA.
(*---*) import IntOrder RealOrder RField.
require import Finite.
require (*--*) FinType.

pragma +implicits.
pragma -oldip.

(* -------------------------------------------------------------------- *)
type 'a distr = 'a Pervasive.distr.

op mass ['a] : 'a distr -> 'a -> real.

axiom muE ['a] (d : 'a distr) (E : 'a -> bool):
  mu d E = sum (fun x => if E x then mass d x else 0%r).

abbrev mu1 (d:'a distr) x = mu d (pred1 x).

axiom massE ['a] (d : 'a distr) x : mass d x = mu1 d x. 

(* -------------------------------------------------------------------- *)
op mk : ('a -> real) -> 'a distr.

inductive isdistr (m : 'a -> real) =
| Distr of
       (forall x, 0%r <= m x)
     & (forall s, uniq s => big predT m s <= 1%r).

lemma ge0_isdistr (d : 'a -> real) x : isdistr d => 0%r <= d x.
proof. by case=> + _; apply. qed.

lemma le1_isdistr (d : 'a -> real) x : isdistr d => d x <= 1%r.
proof. by case=> _ /(_ [x] _) //; rewrite big_seq1. qed.

lemma le1_sum_isdistr (d : 'a -> real) s :
  isdistr d => uniq s => big predT d s <= 1%r.
proof. by case=> _; apply. qed.

axiom distrW (P : 'a distr -> bool):
  (forall m, isdistr m => P (mk m)) => forall d, P d.

axiom muK (m : 'a -> real): isdistr m => mass (mk m) = m.
axiom mkK (d : 'a distr): mk (mass d) = d.

lemma ge0_mass ['a] (d : 'a distr) (x : 'a) : 0%r <= mass d x.
proof. by elim/distrW: d x => m dm; rewrite muK //; case: dm. qed.

lemma le1_mass ['a] (d : 'a distr) (s : 'a list) :
  uniq s => big predT (mass d) s <= 1%r.
proof. by elim/distrW: d s => m dm; rewrite muK //; case: dm. qed.

lemma isdistr_mass (d : 'a distr) : isdistr (mass d).
proof. split; [exact/ge0_mass | exact/le1_mass]. qed.

lemma isdistr_mu1 (d : 'a distr): isdistr (mu1 d).
proof.
have [_ <-] := (fun_ext (mass d) (mu1 d)).
+ by move=> x; apply/massE. + by apply/isdistr_mass.
qed.

lemma ge0_mu1 (d : 'a distr) x : 0%r <= mu1 d x.
proof. by rewrite -massE ge0_mass. qed.

lemma le1_mu1 (d : 'a distr) x : mu1 d x <= 1%r.
proof.
by have := le1_mass d [x] _ => //; rewrite big_seq1 -massE.
qed.

lemma summable_mass ['a] (d : 'a distr) : summable (mass d).
proof.
exists 1%r=> s eq_s; rewrite (@eq_bigr _ _ (mass d)) => /=.
  by move=> i _; rewrite ger0_norm // ge0_mass.
by apply/le1_mass.
qed.

lemma countable_mass ['a] (d : 'a distr):
  countable (fun x => mass d x <> 0%r).
proof. by apply/sbl_countable/summable_mass. qed.

lemma eq_distr_mass (d1 d2 : 'a distr):
  (d1 = d2) <=> (forall x, mass d1 x = mass d2 x).
proof.
split=> [->//|eq_mu]; rewrite -(@mkK d1) -(@mkK d2).
by congr; apply/fun_ext.
qed.

lemma eq_distr (d1 d2 : 'a distr):
  (d1 = d2) <=> (forall x, mu1 d1 x = mu1 d2 x).
proof.
by split=> [->//|h]; apply/eq_distr_mass=> x; rewrite !massE h.
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
+ by rewrite -(@eq_summable (mass d)) ?summable_mass.
+ by move=> x @/predT /=; apply/ge0_mass.
qed.

lemma weightE (d : 'a distr) : weight d = sum (mass d).
proof. by rewrite muE; apply/eq_sum=> x /=. qed.

lemma weight_eq0 ['a] (d : 'a distr) :
  weight d = 0%r => (forall x, mu1 d x = 0%r).
proof.
move=> h x; move: h; apply: contraLR => nz_mux; rewrite weightE.
suff h: 0%r < sum (mass d) by rewrite gtr_eqF.
have gt0_mux: 0%r < mu1 d x.
+ by rewrite ltr_neqAle eq_sym nz_mux ge0_mu1.
pose d' := fun y => if x = y then mu1 d x else 0%r.
apply (@ltr_le_trans (sum d')); first rewrite (@sumE_fin _ [x]) //.
+ by move=> y @/d'; case: (x = y) => [->|].
+ by rewrite big_seq1.
apply/RealSeries.ler_sum.
+ by move=> y; rewrite massE /d'; case: (x = y) => // _; apply/ge0_mu1.
+ (* factor out - finite support stuffs are summable *)
  exists (mu1 d x) => J uq_J; case: (x \in J) => h; last first.
  * rewrite big_seq big1 ?ge0_mu1 // => y /= yJ @/d'.
    by case: (x = y) => [->>//|]; rewrite normr0.
  rewrite (@bigD1 _ _ x) //= big1 /=.
  * by move=> y @/predC1 @/d'; rewrite eq_sym => ->; rewrite normr0.
  by rewrite /d' /= ger0_norm // ge0_mu1.
+ by apply/summable_mass.
qed.

(* -------------------------------------------------------------------- *)
op support (d : 'a distr) x = 0%r < mu1 d x.

abbrev (\in) (x : 'a) (d : 'a distr) = support d x.
abbrev (\notin) (x : 'a) (d : 'a distr) = !support d x.

lemma supportP (d : 'a distr) x : support d x = (0%r <> mu1 d x).
proof. by rewrite eqr_le -massE ge0_mass /= lerNgt massE. qed.

pred is_lossless (d : 'a distr) = weight d = 1%r.

pred is_full (d : 'a distr) = forall x, x \in d.

pred is_uniform (d : 'a distr) = forall (x y:'a),
  x \in d => y \in d => mu1 d x = mu1 d y.

pred is_funiform (d:'a distr) = forall (x y:'a),  mu1 d x = mu1 d y.

lemma is_full_funiform (d:'a distr) : 
  is_full d => is_uniform d => is_funiform d.
proof. by move=> Hf Hu x y;apply Hu;apply Hf. qed.

lemma nosmt funi_uni (d:'a distr) : is_funiform d => is_uniform d.
proof. by move=> H ????;apply H. qed.

(* -------------------------------------------------------------------- *)
axiom mu_bounded (d:'a distr) (p:'a -> bool) : 0%r <= mu d p <= 1%r.

lemma ge0_mu (d : 'a distr) p : 0%r <= mu d p.
proof. by case: (mu_bounded d p). qed.

lemma le1_mu (d : 'a distr) p : mu d p <= 1%r.
proof. by case: (mu_bounded d p). qed.

axiom mu_le (d:'a distr) (p q:'a -> bool):
  (forall x, x \in d => p x => q x) =>
  mu d p <= mu d q.

lemma mu_sub (d:'a distr) (p q:('a -> bool)):
  p <= q => mu d p <= mu d q.
proof. by move=> le_pq; apply/mu_le => ??; apply/le_pq. qed.

lemma mu_eq (d:'a distr) (p q:'a -> bool):
  p == q => mu d p = mu d q.
proof.
by move=> ext_p_q; congr=> //; apply fun_ext.
qed.

lemma mu_eq_support : forall (d : 'a distr) (p q : 'a -> bool),
  (forall (x : 'a), x \in d => p x = q x) => mu d p = mu d q.
proof. smt (mu_le). qed.

lemma mu0 (d : 'a distr) : mu d pred0 = 0%r.
proof. by rewrite muE /pred0 /= sum0. qed.

lemma mu0_false ['a] (d : 'a distr) (p : 'a -> bool) :
  (forall x, x \in d => !p x) => mu d p = 0%r.
proof. by rewrite -(@mu0 d)=> H;apply mu_eq_support => x /H ->. qed.

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

axiom witness_support P (d : 'a distr) :
  0%r < mu d P <=> (exists x, P x /\ x \in d).

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
apply/ler_pemulr; first by apply/ge0_mu1.
by rewrite le_fromint -(@ltzE 0) -has_count has_pred1.
qed.

lemma mu_mem_le_mu1 ['a] (d : 'a distr) (s : 'a list) r :
  (forall x, mu1 d x <= r) => mu d (mem s) <= (size s)%r * r.
proof.
move=> le; apply/(ler_trans (big predT (fun (x : 'a) => r) s)).
+ by have := mu_mem_le d s => /ler_trans; apply; apply/ler_sum.
by rewrite Bigreal.sumr_const count_predT.
qed.

(* -------------------------------------------------------------------- *)
lemma uniform_finite ['a] (d : 'a distr) :
  is_uniform d => is_finite (support d).
proof.
move=> uf_d; case: (is_finite (support d)) => //.
(* FIXME: not having the explicit proof arg leads to InvalidGoalShape *)
move=> ^h /(NfiniteP 1 _ lez01) [] [//|x s [_] xsd].
have {xsd s} xd: x \in d by apply/xsd.
pose r := 1 + ceil (1%r / mu1 d x).
have ge0_cr: 0 <= r by smt(ceil_bound).
case/(NfiniteP _ _ ge0_cr): h => s [[sz_s uq_s] les].
have := le1_mu d (mem s); rewrite mu_mem_uniq //.
rewrite big_seq -(@eq_bigr _ (fun _ => mu1 d x)).
+ by move=> y /= /les yd; apply/uf_d.
rewrite -big_seq Bigreal.sumr_const count_predT negP -ltrNge.
apply/(@ltr_le_trans (r%r * mu1 d x)); last first.
+ by apply/ler_wpmul2r/le_fromint => //; apply/ge0_mu1.
by have: 0%r <> mu1 d x; [rewrite ltr_eqF | smt(ceil_bound)].
qed.

lemma mu1_uni ['a] (dt : 'a distr) x : 
  is_uniform dt => 
  mu1 dt x = if x \in dt then weight dt / (size (to_seq (support dt)))%r else 0%r.
proof.
  move=> dt_uni;case: (x \in dt) => Hx; 2: by smt (mu_bounded).
  have Hf:= uniform_finite dt dt_uni.
  have : mu dt (mem (to_seq (support dt))) = weight dt.  
  + by apply mu_eq_support => ?;rewrite mem_to_seq 1:// => ->.
  rewrite mu_mem_uniq 1:uniq_to_seq //.
  have -> : BRA.big predT (fun (x0 : 'a) => mu1 dt x0) (to_seq (support dt)) = 
            BRA.big predT (fun (x0 : 'a) => mu1 dt x) (to_seq (support dt)).
  + by apply BRA.congr_big_seq => // z;rewrite mem_to_seq //= => ? _ _;apply dt_uni.
  rewrite Bigreal.sumr_const count_predT=> <-;field.
  have /has_predT /lt_fromint /#: has predT (to_seq (support dt)).
  by rewrite hasP;exists x;rewrite mem_to_seq.
qed.

lemma mu1_uni_ll ['a] (dt : 'a distr) x : 
  is_uniform dt => is_lossless dt => 
  mu1 dt x = if x \in dt then 1%r/ (size (to_seq (support dt)))%r else 0%r.
proof. by move=> dt_uni dt_ll; rewrite mu1_uni // dt_ll. qed.

(* -------------------------------------------------------------------- *)
op mnull ['a] = fun (x : 'a) => 0%r.
op dnull ['a] = mk mnull<:'a>.

lemma isdistr_mnull ['a] : isdistr mnull<:'a>.
proof. by split=> //= s _; rewrite Bigreal.sumr_const mulr0. qed.

lemma dnull1E ['a] : forall x, mu1 dnull<:'a> x = 0%r.
proof. by move=> x; rewrite -massE muK //; apply/isdistr_mnull. qed.

lemma dnullE ['a] (E : 'a -> bool) : mu dnull<:'a> E = 0%r.
proof.
rewrite muE -(@eq_sum (fun x=> 0%r)) 2:sum0 //.
by move=> x /=; rewrite massE dnull1E if_same.
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
  by split=> [le0_dx|->] //; apply/ler_asym; rewrite le0_dx -massE ge0_mass.
by move=> h; apply/eq_distr=> x; rewrite h dnull1E.
qed.

lemma weight_eq0_dnull ['a] (d : 'a distr) : weight d = 0%r => d = dnull.
proof.
by move=> /weight_eq0 dx_eq0; apply/eq_distr=> x; rewrite dnull1E dx_eq0.
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
rewrite !max_ler ?size_ge0; case: (s1 = []) => [^/eqvnil -> ->//|nz_s1].
rewrite !IntOrder.pmulr_rgt0 ?lt0n ?size_ge0 ?size_eq0 -?eqvnil //.
by rewrite count_ge0. by rewrite count_ge0.
qed.

op mrat ['a] (s : 'a list) =
  fun x => (count (pred1 x) s)%r / (size s)%r.

lemma isdistr_drat (s : 'a list) : isdistr (mrat s).
proof.
rewrite /mrat; split=> /= [x|J uq_J].
  by rewrite divr_ge0 // le_fromint ?(count_ge0, size_ge0).
rewrite -divr_suml -sumr_ofint. admit.
qed.

op drat ['a] (s : 'a list) = mk (mrat s).

lemma dratE ['a] (s : 'a list) (x : 'a):
  mu1 (drat s) x = (count (pred1 x) s)%r / (size s)%r.
proof. by rewrite -massE muK // isdistr_drat. qed.

lemma prratE ['a] (s : 'a list) (E : 'a -> bool) :
  mu (drat s) E = (count E s)%r / (size s)%r.
proof.
rewrite muE (@sumE_fin _ (undup s)) ?undup_uniq //=.
  move=> x; case: (E x)=> _ //; rewrite massE dratE.
  rewrite mulf_eq0 negb_or mem_undup eq_fromint => -[+ _].
  by rewrite -lt0n ?count_ge0 // -has_count has_pred1.
pose F := fun x => (count (pred1 x) s)%r / (size s)%r.
rewrite -big_mkcond (@eq_bigr _ _ F) /F /= => {F}.
  by move=> i _; rewrite massE dratE.
by rewrite -size_filter -divr_suml -sumr_ofint big_count.
qed.

lemma supp_drat (s : 'a list) x : x \in (drat s) <=> x \in s.
proof.
rewrite /support dratE -has_pred1 has_count.
case: (count (pred1 x) s <= 0); [smt w=count_ge0|].
move=> /IntOrder.ltrNge ^ + -> /=; rewrite -lt_fromint; case: s=> //=.
move=> ? s /(@mulr_gt0 _ (inv (1 + size s)%r)) -> //.
by rewrite invr_gt0 lt_fromint [smt w=size_ge0].
qed.

lemma eq_dratP ['a] (s1 s2 : 'a list) :
  eq_ratl s1 s2 <=> (drat s1 = drat s2).
proof.
split=> [[]|eq_d].
  move=> eqvnil eq_s12; apply/eq_distr=> x; rewrite !dratE.
  move/perm_eqP/(_ (pred1 x)): eq_s12; rewrite !count_flatten_nseq.
  rewrite !max_ler ?size_ge0; case: (s1 = []).
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
rewrite !max_ler ?addr_ge0 ?size_ge0 // eqf_div;
  try by rewrite eq_fromint add1z_neq0 ?size_ge0.
by rewrite -!fromintM eq_fromint !(@mulzC (1 + _)).
qed.

lemma eq_sz_dratP ['a] (s1 s2 : 'a list) : size s1 = size s2 =>
  perm_eq s1 s2 <=> (drat s1 = drat s2).
proof.
move=> eq_sz; rewrite -eq_dratP /eq_ratl -!size_eq0 -!eq_sz /=.
split=> /perm_eqP eq; apply/perm_eqP=> p; rewrite ?count_flatten_nseq ?eq //.
move/(_ p): eq; rewrite !count_flatten_nseq max_ler ?size_ge0.
case: (s1 = []) => [->>|] /=.
  suff ->//: s2 = []; by rewrite -size_eq0 eq_sz.
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


end MFinite.

(* -------------------------------------------------------------------- *)
theory MIntUniform.

op drange (m n : int) = MUniform.duniform (range m n).

lemma drange1E (m n x : int):
  mu1 (drange m n) x = if m <= x < n then 1%r / (n - m)%r else 0%r.
proof.
rewrite MUniform.duniform1E mem_range undup_id 1:range_uniq //.
rewrite size_range; case: (m <= x < n) => // -[le_mx lt_xn].
rewrite max_ler // IntOrder.subr_ge0 IntOrder.ltrW //.
by apply (IntOrder.ler_lt_trans _ le_mx).
qed.

lemma drangeE (E : int -> bool) (m n : int) :
  mu (drange m n) E = (count E (range m n))%r / (n - m)%r.
proof.
rewrite MUniform.duniformE undup_id 1:range_uniq //.
rewrite size_range; case: (lezWP n m) => [le_nm|le_mn].
  by rewrite max_lel // 1:subr_le0 // range_geq //.
by rewrite max_ler // subr_ge0 ltrW // ltzNge.
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
op mlet ['a 'b] (d : 'a distr) (f : 'a -> 'b distr) =
  fun (y : 'b) => sum<:'a> (fun x => mass d x * mass (f x) y).

op dlet ['a 'b] (d : 'a distr) (f : 'a -> 'b distr) =
  mk (mlet d f).

lemma isdistr_mlet ['a 'b] (d : 'a distr) (f : 'a -> 'b distr) :
  isdistr (mlet d f).
proof. admit. qed.

lemma dlet_massE (d : 'a distr) (f : 'a -> 'b distr) (b : 'b):
  mass (dlet d f) b = sum<:'a> (fun a => mass d a * mass (f a) b).
proof. by rewrite muK 1:isdistr_mlet /mlet &(eq_sum). qed.

lemma dlet1E (d : 'a distr) (f : 'a -> 'b distr) (b : 'b):
  mu1 (dlet d f) b = sum<:'a> (fun a => mu1 d a * mu1 (f a) b).
proof. 
by rewrite -massE dlet_massE &(eq_sum) => x /=; rewrite !massE.
qed.

lemma dletE (d : 'a distr) (f : 'a -> 'b distr) (P : 'b -> bool):
  mu (dlet d f) P
  = sum<:'b> (fun b =>
      sum<:'a> (fun a =>
        if P b then mass d a * mass (f a) b else 0%r)).
proof.
  rewrite muE; have:= dlet_massE d f; rewrite -(@fun_ext (mass _)) => -> /=.
  by apply/eq_sum=> /= b; case: (P b)=> //=; rewrite sum0.
qed.

lemma dletE_swap (d : 'a distr) (f : 'a -> 'b distr) (P : 'b -> bool):
  mu (dlet d f) P
  = sum<:'a> (fun a =>
      sum<:'b> (fun b =>
        if P b then mass d a * mass (f a) b else 0%r)).
proof. rewrite dletE. admit (* swapping convergent sums *). qed.

lemma weight_dlet (d:'a distr) (F:'a -> 'b distr) :
  weight (dlet d F) <= weight d.
proof. admit. qed.

lemma supp_dlet (d : 'a distr) (F : 'a -> 'b distr) (b : 'b) :
  b \in (dlet d F) <=> exists a, a \in d /\ b \in (F a).
proof.
have ->: (exists a, a \in d /\ b \in (F a))
         <=> exists a, mu1 d a * mu1 (F a) b <> 0%r.
+ apply/exists_iff;smt w=mu_bounded.
rewrite /support dlet1E.
admit (* a positive sum is non-zero iff one of its terms is non-zero *).
qed.

lemma nosmt dlet_d_unit (d:'a distr) : dlet d MUnit.dunit = d.
proof.
apply/eq_distr=> x; rewrite dlet1E /mlet /=.
rewrite (@sumE_fin _ [x]) //=.
+ by move=> x0; rewrite MUnit.dunit1E /=; case (x0 = x).
by rewrite big_consT big_nil /= MUnit.dunit1E.
qed.

lemma nosmt dlet_unit (F:'a -> 'b distr) a : dlet (MUnit.dunit a) F = F a.
proof.
apply/eq_distr=> x; rewrite dlet1E /mlet /=.
rewrite (@sumE_fin _ [a]) //=.
+ by move=> a0; rewrite MUnit.dunit1E (@eq_sym a); case (a0 = a).
by rewrite big_consT big_nil /= MUnit.dunit1E.
qed.

lemma dlet_dlet (d1:'a distr) (F1:'a -> 'b distr) (F2: 'b -> 'c distr):
  dlet (dlet d1 F1) F2 = dlet d1 (fun x1 => dlet (F1 x1) F2).
proof.
apply/eq_distr_mass=> c. rewrite !massE !dletE.
apply eq_sum=> c' /= ; case: (c' = c)=> //= ->;2:by rewrite !sum0.
move=> {c'} @/pred1 /=.
admit.
qed.

lemma dlet_dnull (F:'a -> 'b distr): dlet dnull F = dnull.
proof.
apply/eq_distr=> x; rewrite dlet1E dnull1E (@sumE_fin _ []) //= => x0.
by rewrite dnull1E.
qed.

lemma dlet_d_dnull (d:'a distr): dlet d (fun a => dnull<:'b>) = dnull.
proof. by apply/eq_distr=> x; rewrite dlet1E dnull1E /= (@sumE_fin _ []). qed.

(* -------------------------------------------------------------------- *)
abbrev dlift (F: 'a -> 'b distr) : 'a distr -> 'b distr =
  fun d => dlet d F.

(* -------------------------------------------------------------------- *)
op dmap ['a 'b] (d : 'a distr) (f : 'a -> 'b) =
  dlet d (MUnit.dunit \o f).

lemma dmap1E (d : 'a distr) (f : 'a -> 'b) (b : 'b):
  mu1 (dmap d f) b = mu d ((pred1 b) \o f).
proof.
rewrite dlet1E muE; apply/eq_sum=> x /=.
by rewrite massE MUnit.dunit1E /preim /pred1 /(\o); case: (f x = b).
qed.

lemma dmapE (d : 'a distr) (f : 'a -> 'b) (P : 'b -> bool):
  mu (dmap d f) P = mu d (P \o f).
proof.
rewrite dletE_swap muE.
apply/eq_sum=> a /=; rewrite (@sumE_fin _ [f a]) //=.
+ by move=> b; rewrite (@eq_sym b) !massE MUnit.dunit1E;case: (f a = b);rewrite /b2r.
by rewrite big_seq1 /= !massE MUnit.dunit1E.
qed.

lemma supp_dmap (d : 'a distr) (f : 'a -> 'b) (b : 'b):
  b \in (dmap d f) <=> exists a, a \in d /\ b = f a.
proof.
rewrite supp_dlet /(\o); apply/exists_eq=> a /=.
by rewrite MUnit.supp_dunit.
qed.

lemma weight_dmap (d : 'a distr) (f : 'a -> 'b) :
  weight (dmap d f) = weight d.
proof. by rewrite (_: predT = preim f predT) // dmapE. qed.

lemma dmap_ll (d : 'a distr) (f : 'a -> 'b) : 
  is_lossless d => is_lossless (dmap d f).
proof. by rewrite /is_lossless weight_dmap. qed.

lemma dmap_unig (d : 'a distr) (f : 'a -> 'b) :
  (forall (x, y : 'a),  0%r < mu1 d y => f x = f y => x = y) => is_uniform d => is_uniform (dmap d f).
proof.
  move=> finj duni x y /supp_dmap [a [ina ->]] /supp_dmap [b [inb ->]].
  rewrite !dmap1E.
  have Heq: forall z, 0%r < mu1 d z => pred1 (f z) \o f = pred1 z.
  + move=> z zin; apply fun_ext => z' @/(\o) @/pred1 /=.
    apply eq_iff => />; apply finj. apply zin.
  by rewrite (Heq ina) (Heq inb); apply duni.
qed.

lemma dmap_uni (d : 'a distr) (f : 'a -> 'b) :
  injective f => is_uniform d => is_uniform (dmap d f).
proof.
  move=> finj; apply dmap_unig; move=> x y _; apply (@finj x y).
qed.

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
  move=> fsurj fu x;rewrite supp_dmap.
  have [a ->]:= fsurj x;exists a => /=;apply fu.
qed.

(* -------------------------------------------------------------------- *)
abbrev dapply (F: 'a -> 'b) : 'a distr -> 'b distr =
  fun d => dmap d F.

(* -------------------------------------------------------------------- *)
theory DScalar.
op mscalar (k : real) (m : 'a -> real) (x : 'a) = k * (m x).

lemma isdistr_mscalar k (m : 'a -> real):
  isdistr m =>
  0%r <= k => k <= inv (weight (mk m)) => isdistr (mscalar k m).
proof.
move=> @/mscalar [] ge0_mx le1_mx ge0_k k_le_invm; split=> [/#|].
move=> s uniq_s.
admit. (* partial sums of a positive sum are bounded by the sum *)
qed.

op dscalar (k : real) (d : 'a distr) = mk (mscalar k (mass d)).

abbrev (\cdot) (k : real) (d : 'a distr) = dscalar k d.

lemma dscalar1E (k : real) (d : 'a distr) (x : 'a):
  0%r <= k => k <= inv (weight d) =>
  mu1 (k \cdot d) x = k * mu1 d x.
proof.
by move=> ge0_k le1_k;rewrite -!massE muK // isdistr_mscalar 1:isdistr_mass 2:mkK.
qed.

lemma dscalarE (k : real) (d : 'a distr) (E : 'a -> bool):
  0%r <= k => k <= inv (weight d) =>
  mu (k \cdot d) E = k * mu d E.
proof.
move=> ge0_k k_le_weight; rewrite muE.
rewrite (@eq_sum _ (fun x=> k * if E x then mu1 d x else 0%r)).
+ by move=> x /=;rewrite massE dscalar1E //; have /= -> := fun_if (fun x=> k * x).
case: (k = 0%r)=> [->|]; first by rewrite sum0.
rewrite muE. admit. (* push non-null scalars out of sums *)
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
  0%r < k => k <= inv (weight d) =>
  is_uniform d => is_uniform (k \cdot d).
proof. 
  move=> gt0k gekw Hu x y;rewrite !dscalar1E // ?ltrW //.
  by rewrite !supp_dscalar // => /Hu H/H ->.
qed.

end DScalar.
export DScalar.

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
apply dscalar_uni =>//; smt (ge0_weight @Real).
qed.

(* -------------------------------------------------------------------- *)
lemma nosmt rnd_funi ['a] (d : 'a distr) :
  is_funiform d => forall x y, mu1 d x = mu1 d y.
proof. by apply. qed.

hint solve 0 random : rnd_funi.
