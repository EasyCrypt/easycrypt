(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2016 - Inria
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
require import Option Pred Fun List Int IntExtra IntDiv Real RealExtra.
require import Ring StdRing StdOrder StdBigop Discrete RealSeq RealSeries.
(*---*) import IterOp Bigint Bigreal Bigreal.BRA.
(*---*) import IntOrder RealOrder RField NewLogic.
require (*--*) FinType.

pragma +implicits.
pragma -oldip.

(* -------------------------------------------------------------------- *)
(* We currently bind old distr/mu_x et al to the new constructs         *)
require export Distr.

type 'a distr = 'a Pervasive.distr.

axiom muE ['a] (d : 'a distr) (E : 'a -> bool):
  mu d E = sum (fun x => if E x then mu_x d x else 0%r).

(* -------------------------------------------------------------------- *)
op mk : ('a -> real) -> 'a distr.

inductive isdistr (m : 'a -> real) =
| Distr of
       (forall x, 0%r <= m x)
     & (forall s, uniq s => big predT m s <= 1%r).

axiom distrW (P : 'a distr -> bool):
  (forall m, isdistr m => P (mk m)) => forall d, P d.

axiom muK (m : 'a -> real): isdistr m => mu_x (mk m) = m.
axiom mkK (d : 'a distr): mk (mu_x d) = d.

lemma ge0_mu_x ['a] (d : 'a distr) (x : 'a):
  0%r <= mu_x d x.
proof. by elim/distrW: d x => m dm; rewrite muK //; case: dm. qed.

lemma le1_mu_x ['a] (d : 'a distr) :
  forall (s : 'a list), uniq s => big predT (mu_x d) s <= 1%r.
proof. by elim/distrW: d => m dm; rewrite muK //; case: dm. qed.

lemma isdistr_mu_x (d : 'a distr): isdistr (mu_x d).
proof. split; [exact/ge0_mu_x|exact/le1_mu_x]. qed.

lemma summable_mu_x ['a] (d : 'a distr) : summable (mu_x d).
proof.
exists 1%r=> s eq_s; rewrite (@eq_bigr _ _ (mu_x d)) => /=.
  by move=> i _; rewrite ger0_norm // ge0_mu_x.
by apply/le1_mu_x.
qed.

lemma ge0_weight ['a] (d : 'a distr) : 0%r <= weight d.
proof.
rewrite -sum0<:'a> muE; apply/RealSeries.ler_sum=> /=; first last.
+ by apply/summable0.
+ by rewrite -(@eq_summable (mu_x d)) ?summable_mu_x.
+ by move=> x @/predT /=; apply/ge0_mu_x.
qed.

lemma weight_eq0 ['a] (d : 'a distr) :
  weight d = 0%r => (forall x, mu_x d x = 0%r).
proof. admit. qed.

lemma countable_mu ['a] (d : 'a distr):
  countable (fun x => mu_x d x <> 0%r).
proof. by apply/sbl_countable/summable_mu_x. qed.

lemma eq_distr (d1 d2 : 'a distr):
  (d1 = d2) <=> (forall x, mu_x d1 x = mu_x d2 x).
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
op mnull ['a] = fun  (x : 'a) => 0%r.
op dnull ['a] = mk mnull<:'a>.

lemma isdistr_mnull ['a] : isdistr mnull<:'a>.
proof. by split=> //= s _; rewrite Bigreal.sumr_const mulr0. qed.

lemma dnull1E ['a] : forall x, mu_x dnull<:'a> x = 0%r.
proof. by move=> x; rewrite muK //; apply/isdistr_mnull. qed.

lemma dnullE ['a] (E : 'a -> bool) : mu dnull<:'a> E = 0%r.
proof.
rewrite muE -(@eq_sum (fun x=> 0%r) _ _) 2:sum0 //.
by move=> x /=; rewrite dnull1E if_same.
qed.

lemma weight_dnumm ['a] : weight dnull<:'a> = 0%r.
proof. by apply/dnullE. qed.

lemma supnullE ['a] : support dnull<:'a> = pred0.
proof. by apply/fun_ext=> x; rewrite /support /in_supp dnull1E. qed.

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
  mu_x (drat s) x = (count (pred1 x) s)%r / (size s)%r.
proof. by rewrite muK // isdistr_drat. qed.

lemma prratE ['a] (s : 'a list) (E : 'a -> bool) :
  mu (drat s) E = (count E s)%r / (size s)%r.
proof.
rewrite muE (@sumE_fin _ (undup s)) ?undup_uniq //=.
  move=> x; case: (E x)=> _ //; rewrite dratE.
  rewrite mulf_eq0 -nor mem_undup eq_fromint => -[+ _].
  by rewrite -lt0n ?count_ge0 // -has_count has_pred1.
pose F := fun x => (count (pred1 x) s)%r / (size s)%r.
rewrite -big_mkcond (@eq_bigr _ _ F) /F /= => {F}.
  by move=> i _; rewrite dratE.
by rewrite -size_filter -divr_suml -sumr_ofint big_count.
qed.

lemma support_drat ['a] (s : 'a list) : support (drat s) = mem s.
proof.
apply/fun_ext=> x; rewrite /support /in_supp dratE.
rewrite eq_iff -has_pred1 has_count.
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
apply/anda_and; split.
  have h: forall t1 t2, drat<:'a> t1 = drat t2 => t1 = [] => t2 = [].
    move=> t1 [|x t2] eq_dt ->>//; move/(congr1 (fun d => mu_x d x)): eq_dt.
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
  mu_x (dunit x) y = if x = y then 1%r else 0%r.
proof. by rewrite MRat.dratE /= /pred1; case: (x = y). qed.

lemma dunit1xx ['a] (x : 'a): mu_x (dunit x) x = 1%r.
proof. by rewrite dunit1E. qed.

lemma dunitE ['a] (E : 'a -> bool) (x : 'a):
  mu (dunit x) E = if E x then 1%r else 0%r.
proof. by rewrite MRat.prratE /=; case: (E x). qed.

lemma dunit_ll ['a] (x : 'a): mu (dunit x) predT = 1%r.
proof. by apply/MRat.drat_ll. qed.

lemma dunit_fu ['a] (x : 'a): support (dunit x) = pred1 x.
proof. by apply/fun_ext=> x'; rewrite MRat.support_drat. qed.
end MUnit.

(* -------------------------------------------------------------------- *)
theory MUniform.
op duniform ['a] (s : 'a list) = MRat.drat (undup s).

lemma duniform1E ['a] (s : 'a list) x :
  mu_x (duniform s) x = if mem s x then 1%r / (size (undup s))%r else 0%r.
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

lemma duniform_fu ['a] (s : 'a list): support (duniform s) = mem s.
proof. by rewrite MRat.support_drat pred_ext=>x; rewrite mem_undup. qed.

lemma duniform_ll (s : 'a list) :
  s <> [] => is_lossless (duniform s).
proof. by move=> nz_s; apply/MRat.drat_ll; rewrite undup_nilp. qed.

lemma duniform_uf (s : 'a list) :
  s <> [] => is_uniform (duniform s).
proof.
move=> s_ne0; rewrite /is_uniform duniform_ll //=.
by move=> x y; rewrite 2!duniform1E duniform_fu=> !->.
qed.
end MUniform.

(* -------------------------------------------------------------------- *)
theory MIntUniform.
op drange (m n : int) = MUniform.duniform (range m n).

lemma drange1E (m n x : int):
  mu_x (drange m n) x = if m <= x < n then 1%r / (n - m)%r else 0%r.
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

lemma support_drange (m n i : int): support (drange m n) i <=> m <= i < n.
proof. by rewrite MRat.support_drat undup_id ?range_uniq mem_range. qed.
end MIntUniform.

(* -------------------------------------------------------------------- *)
op mlet ['a 'b] (d : 'a distr) (f : 'a -> 'b distr) =
  fun (y : 'b) => sum<:'a> (fun x => mu_x d x * mu_x (f x) y).

op dlet ['a 'b] (d : 'a distr) (f : 'a -> 'b distr) =
  mk (mlet d f).

lemma isdistr_mlet ['a 'b] (d : 'a distr) (f : 'a -> 'b distr) :
  isdistr (mlet d f).
proof. admit. qed.

lemma mux_dlet (d : 'a distr) (f : 'a -> 'b distr) (b : 'b):
  mu_x (dlet d f) b = sum<:'a> (fun a => mu_x d a * mu_x (f a) b).
proof. by rewrite muK 1:isdistr_mlet. qed.

lemma mu_dlet (d : 'a distr) (f : 'a -> 'b distr) (P : 'b -> bool):
  mu (dlet d f) P
  = sum<:'b> (fun b =>
      sum<:'a> (fun a =>
        if P b then mu_x d a * mu_x (f a) b else 0%r)).
proof.
rewrite muE; have:= mux_dlet d f; rewrite (@fun_ext (mu_x _))=> -> /=.
by apply/eq_sum=> /= b; case: (P b)=> //=; rewrite sum0.
qed.

lemma mu_dlet_swap (d : 'a distr) (f : 'a -> 'b distr) (P : 'b -> bool):
  mu (dlet d f) P
  = sum<:'a> (fun a =>
      sum<:'b> (fun b =>
        if P b then mu_x d a * mu_x (f a) b else 0%r)).
proof. rewrite mu_dlet. admit (* swapping convergent sums *). qed.

lemma weight_dlet (d:'a distr) (F:'a -> 'b distr) :
  weight (dlet d F) <= weight d.
proof. admit. qed.

lemma support_dlet (d : 'a distr) (F : 'a -> 'b distr) (b : 'b) :
  support (dlet d F) b <=> exists a, support d a /\ support (F a) b.
proof.
have ->: (exists a, support d a /\ support (F a) b)
         <=> exists a, mu_x d a * mu_x (F a) b <> 0%r.
(* Note: mu_bounded is disappearing *)
+ by apply/exists_iff=> a /= @/support @/in_supp; smt w=mu_bounded.
rewrite /support /in_supp mux_dlet.
admit (* a positive sum is non-zero iff one of its terms is non-zero *).
qed.

lemma nosmt dlet_d_unit (d:'a distr) : dlet d MUnit.dunit = d.
proof.
apply/eq_distr=> x; rewrite mux_dlet /mlet /=.
rewrite (@sumE_fin _ [x]) //=.
+ by move=> x0; rewrite MUnit.dunit1E /=; case (x0 = x).
by rewrite big_consT big_nil /= MUnit.dunit1E.
qed.

lemma nosmt dlet_unit (F:'a -> 'b distr) a : dlet (MUnit.dunit a) F = F a.
proof.
apply/eq_distr=> x; rewrite mux_dlet /mlet /=.
rewrite (@sumE_fin _ [a]) //=.
+ by move=> a0; rewrite MUnit.dunit1E (@eq_sym a); case (a0 = a).
by rewrite big_consT big_nil /= MUnit.dunit1E.
qed.

lemma dlet_dlet (d1:'a distr) (F1:'a -> 'b distr) (F2: 'b -> 'c distr):
  dlet (dlet d1 F1) F2 = dlet d1 (fun x1 => dlet (F1 x1) F2).
proof.
apply/eq_distr=> c; rewrite !mu_dlet /=.
apply eq_sum=> c' /= @/pred1; case: (c' = c)=> //=; 2: by rewrite !sum0.
move=> ->> {c'}.
admit.
qed.

lemma dlet_dnull (F:'a -> 'b distr): dlet dnull F = dnull.
proof.
apply/eq_distr=> x; rewrite mux_dlet dnull1E (@sumE_fin _ []) //= => x0.
by rewrite dnull1E.
qed.

lemma dlet_d_dnull (d:'a distr): dlet d (fun a => dnull<:'b>) = dnull.
proof. by apply/eq_distr=> x; rewrite mux_dlet dnull1E /= (@sumE_fin _ []). qed.

(* -------------------------------------------------------------------- *)
abbrev dlift (F: 'a -> 'b distr) : 'a distr -> 'b distr =
  fun d => dlet d F.

(* -------------------------------------------------------------------- *)
op dmap ['a 'b] (d : 'a distr) (f : 'a -> 'b) =
  dlet d (MUnit.dunit \o f).

lemma mux_dmap (d : 'a distr) (f : 'a -> 'b) (b : 'b):
  mu_x (dmap d f) b = mu d ((pred1 b) \o f).
proof.
rewrite muE mux_dlet; apply/eq_sum=> x /=.
by rewrite MUnit.dunit1E /preim /pred1 /(\o); case: (f x = b).
qed.

lemma mu_dmap (d : 'a distr) (f : 'a -> 'b) (P : 'b -> bool):
  mu (dmap d f) P = mu d (P \o f).
proof.
rewrite mu_dlet_swap muE.
apply/eq_sum=> a /=; rewrite (@sumE_fin _ [f a]) //=.
+ by move=> b; rewrite (@eq_sym b) MUnit.dunit1E; case: (f a = b).
by rewrite big_seq1 /= MUnit.dunit1E.
qed.

lemma support_dmap (d : 'a distr) (f : 'a -> 'b) (b : 'b):
  support (dmap d f) b <=> exists a, support d a /\ b = f a.
proof.
rewrite support_dlet /(\o); apply/exists_eq=> a /=.
by rewrite MUnit.dunit_fu.
qed.

lemma weight_dmap (d : 'a distr) (f : 'a -> 'b):
  weight (dmap d f) = weight d.
proof. by rewrite /weight {2}(_: predT = preim f predT) // mu_dmap. qed.

(* -------------------------------------------------------------------- *)
abbrev dapply (F: 'a -> 'b) : 'a distr -> 'b distr =
  fun d => dmap d F.

(* -------------------------------------------------------------------- *)
op mscale ['a] (d : 'a distr) =
  fun x => mu_x d x / weight d.

op dscale ['a] (d : 'a distr) =
  mk (mscale d).

lemma isdistr_mscale (d : 'a distr) : isdistr (mscale d).
proof.
split=> @/mscale [x|s uqs].
  by rewrite divr_ge0 1:ge0_mu_x // ge0_weight.
rewrite -divr_suml; apply/(@ler_trans (weight d / weight d)).
  rewrite ler_wpmul2r // ?invr_ge0 ?ge0_weight //.
  admit.
have := ge0_weight d; rewrite ler_eqVlt => -[<-|gt0_iw].
  by rewrite divr0. by rewrite divrr // gtr_eqF.
qed.

lemma mux_dscale ['a] (d : 'a distr) (x : 'a) :
  mu_x (dscale d) x = mu_x d x / weight d.
proof. by rewrite muK 1:isdistr_mscale. qed.

lemma mu_dscale ['a] (d : 'a distr) (E : 'a -> bool) :
  mu (dscale d) E = mu d E / weight d.
proof.
rewrite muE. have:= mux_dscale d.
rewrite fun_ext -(@etaE (mu_x (dscale d))) etaP=> -> /=.
apply/(@eq_trans _ ((sum (fun x=> if E x then mu_x d x else 0%r)) / weight d)).
+ admit. (* push constant multiplicative factors out of sums when non-null *)
by rewrite -muE.
qed.

lemma weight_dscale ['a] (d : 'a distr) :
  weight (dscale d) = if weight d = 0%r then 0%r else 1%r.
proof.
rewrite mu_dscale -/(weight _); case: (weight d = 0%r)=> //= [->|].
+ exact/divr0.
exact/unitrE.
qed.

lemma support_dscale ['a] (d : 'a distr) :
  support (dscale d) = support d.
proof.
rewrite -fun_ext /support /in_supp=> x; rewrite eq_iff mux_dscale.
case: (weight d = 0%r)=> [^/weight_eq0 -> ->|d_nonempty].
+ by rewrite divr0.
smt w=ge0_weight.
qed.

(* -------------------------------------------------------------------- *)
abstract theory MFinite.
type t.

clone import FinType as Support with type t <- t.

op dunifin : t distr = MUniform.duniform enum.

lemma dunifin1E (x : t) : mu_x dunifin x = 1%r / (size enum)%r.
proof. by rewrite MUniform.duniform1E enumP /= undup_id // enum_uniq. qed.

lemma dunifinE (E : t -> bool) :
  mu dunifin E = (count E enum)%r / (size enum)%r.
proof. by rewrite MUniform.duniformE ?undup_id // enum_uniq. qed.

lemma dunifin_ll : is_lossless dunifin.
proof.
rewrite MUniform.duniform_ll -size_eq0 -lt0n.
  by rewrite size_ge0. by rewrite Support.card_gt0.
qed.

lemma duniform_fu: support dunifin = predT.
proof.
rewrite MUniform.duniform_fu; apply/fun_ext.
by move=> x; rewrite Support.enumP.
qed.
end MFinite.
