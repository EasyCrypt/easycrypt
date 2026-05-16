(* -------------------------------------------------------------------- *)
require import Bool AllCore List Finite Discrete.
require import StdRing StdOrder StdBigop RealLub RealSeq.
(*---*) import IterOp Bigint Bigreal Bigreal.BRA.
(*---*) import Ring.IntID IntOrder RField RealOrder.

pragma +implicits.

(* -------------------------------------------------------------------- *)
op partial (s : int -> real) (n : int) : real =
  bigi predT s 0 n.

op convergeto (s : int -> real) (x : real) =
  RealSeq.convergeto (partial s) x.

op converge (s : int -> real) =
  exists x, convergeto s x.

(* -------------------------------------------------------------------- *)
op summable (s : 'a -> real) =
  exists M, forall J,
    uniq J => big predT (fun i => `|s i|) J <= M.

(* -------------------------------------------------------------------- *)
lemma sbl_countable (s : 'a -> real) :
  summable s => countable (fun i => s i <> 0%r).
proof.
pose E i := fun x => if i <= 0 then false else 1%r / i%r <= `|s x|.
case=> M sbl_s; have: 0%r <= M.
+ apply/(@ler_trans `|s witness|); 1: by apply/normr_ge0.
  by have := sbl_s [witness] _ => //; rewrite big_seq1.
rewrite ler_eqVlt => -[<<-|gt0_M]; 1: apply: countable0_eq.
+ apply/fun_ext=> x; apply/negbTE => /=; have := sbl_s [x] _ => //.
  by rewrite big_seq1 /= normr_le0.
have fin_E: forall i, countable (E i); 1: (move=> i; apply/cnt_finite).
+ move=> @/E; case: (i <= 0) => [_|/ltzNge gt0_i]; 1: by apply/finite0.
  apply/negbNE/negP; pose n := i * (intp M + 1); have ge0_n: 0 <= n.
  - rewrite &(IntOrder.ler_trans i) 1:ltrW // ler_pmulr //.
    by rewrite ler_addr &(leup_intp) ltrW.
  case/(@NfiniteP n _ ge0_n) => J [[szJ uqJ] memJ].
  have := sbl_s _ uqJ; pose S := big _ _ _; move=> leSM.
  suff: M < S by apply: (ler_lt_trans _ leSM).
  apply/(@ltr_le_trans (big predT (fun _ => 1%r / i%r) J)); last first.
  - by rewrite /S !big_seq; apply/ler_sum=> x /= Px; apply/memJ.
  rewrite sumr_const intmulr count_predT mulrAC /=.
  apply/(ltr_le_trans (n%r / i%r)); last first.
  rewrite ler_pmul2r ?invr_gt0 1..2:(lt_fromint, le_fromint) //.
  by rewrite /n fromintM mulrAC divff /= ?gt_intp eq_fromint gtr_eqF.
have Efu: forall x, s x <> 0%r => exists i, E i x.
+ move=> x nz_sx; case: (1%r <= `|s x|) => [|/ltrNge gt1_sx].
  - by move=> h; exists 1.
  exists (intp (inv `|s x|) + 1) => @/E; rewrite -if_neg.
  rewrite -ltrNge ltzS leup_intp 1:invr_ge0 1:normr_ge0 //=.
  apply/(@ler_pdivr_mulr (intp (inv (`|s x|)) + 1)%r _ 1%r).
  - by rewrite lt_fromint ltzS leup_intp invr_ge0 normr_ge0.
  apply/ltrW/(@ler_lt_trans (`|s x| / `|s x|)).
  - by rewrite divff ?normr0P.
  by rewrite ltr_pmul2l ?normr_gt0 // gt_intp.
by apply/(@countable_le (fun x => exists i, E i x)); 1: apply/cnt_Uw.
qed.

(* -------------------------------------------------------------------- *)
op support ['a] (s : 'a -> real) = fun x => s x <> 0%r.

(* -------------------------------------------------------------------- *)
lemma summable0: summable (fun (x:'a) => 0%r).
proof. by exists 0%r=> J uqJ; rewrite Bigreal.sumr_const normr0. qed.

(* -------------------------------------------------------------------- *)
lemma summable_fin ['a] s (J : 'a list) :
  (forall x, s x <> 0%r => x \in J) => summable s.
proof.
move=> hfin; exists (BRA.big predT (fun x => `|s x|) (undup J)).
move=> K uqK; rewrite (@BRA.bigID _ _ (mem J)) addrC BRA.big1 /=.
+ by move=> x [_ @/predC] /=; apply: contraR; rewrite normr0P &(hfin).
rewrite -BRA.big_filter (@BRA.bigID _ _ (mem K) (undup J)).
rewrite -!(@BRA.big_filter (predI _ _)) /= ler_paddr.
+ by apply: Bigreal.sumr_ge0 => /= a _; rewrite normr_ge0.
apply/lerr_eq/BRA.eq_big_perm.
rewrite uniq_perm_eq ?filter_uniq ?undup_uniq //.
by move=> x; rewrite !mem_filter mem_undup andbC.
qed.

(* -------------------------------------------------------------------- *)
lemma summable_from_bounded (s : 'a -> real) :
  forall (J : int -> 'a option),
       enumerate J (support s)
    => (exists M, forall n, big predT (fun a => `|s a|) (pmap J (range 0 n)) <= M)
    => summable s.
proof.
move=> J enm [M hb]; exists M => l hl.
have [n hn] := enumerate_pmap_range J l (support s) enm.
pose I := pmap J (range 0 n).
apply: (ler_trans (big predT (fun (a : 'a) => `|s a|) I)); last by apply hb.
rewrite (@big_eq_idm_filter (support s)); 1:smt().
rewrite (@partition_big (fun x => x) _ predT _ _ I).
+ apply: pmap_inj_in_uniq; last by apply range_uniq.
  by move=> i j v _ _; case: enm => h _; apply/h.
+ by move=> a hin hs /=; rewrite /predT /=; apply /hn.
apply: sub_ler_sum => // a /= _.
by rewrite (@bigD1_cond_if _ _ _ a) //= big1 /#.
qed.

(* -------------------------------------------------------------------- *)
lemma eq_summable (s1 s2 : 'a -> real):
  (forall x, s1 x = s2 x) => summable s1 <=> summable s2.
proof. by move=> /fun_ext ->. qed.

(* -------------------------------------------------------------------- *)
lemma eqL_summable (s1 s2 : 'a -> real):
  summable s1 => (forall x, s1 x = s2 x) => summable s2.
proof. by move=> sm1 /eq_summable <-. qed.

(* -------------------------------------------------------------------- *)
lemma eqL_notin_summable (I : 'a list) (s1 s2 : 'a -> real)  :
  (forall x, !x \in I => s1 x = s2 x) => summable s1 => summable s2.
proof.
move => eq_J_s1_s2 [M sum_s1].
pose R := big predT (fun x => `|s2 x|) (undup I).
exists (M+R) => J uniq_J.
rewrite (@bigEM (mem I)) addrC &(ler_add).
- rewrite (@eq_bigr _ _ (fun x => `|s1 x|)) //= 1:/#.
  rewrite -big_filter. by apply /sum_s1 /filter_uniq.
- have P : perm_eq (filter (mem I) J) (filter (mem J) (undup I)).
    by apply: uniq_perm_eq; smt(filter_uniq undup_uniq mem_filter mem_undup).
  rewrite -big_filter (eq_big_perm P) big_filter big_mkcond.
  by apply ler_sum => /= /#.
qed.

(* -------------------------------------------------------------------- *)
lemma summable_le (s2 s1 : 'a -> real) :
     summable s2
  => (forall x, `|s1 x| <= `|s2 x|)
  => summable s1.
proof.
by case=> M h le_s12; exists M => J /h; apply/ler_trans/Bigreal.ler_sum.
qed.

(* -------------------------------------------------------------------- *)
lemma summable_norm (s : 'a -> real):
  summable s => summable (fun x => `|s x|).
proof.
case=> M leM; exists M => J /leM le; apply: (ler_trans _ _ le).
by apply/lerr_eq/eq_bigr => x _ /=; rewrite normr_id.
qed.

lemma norm_summable (s : 'a -> real) : 
  summable (fun x => `|s x|) => summable s.
proof. 
move => sum_s; apply (summable_le _ sum_s) => /= a. 
by rewrite (@ger0_norm `|s a|) ?normr_ge0.
qed.

(* -------------------------------------------------------------------- *)
lemma summableD (s1 s2 : 'a -> real):
  summable s1 => summable s2 => summable (fun x => s1 x + s2 x).
proof.
move=> [M1 leM1] [M2 leM2]; exists (M1 + M2)=> J uqJ.
have /ler_add /(_ _ _ (leM2 J _)) := leM1 _ uqJ => // le.
apply/(ler_trans _ _ le); rewrite -big_split /=; apply/ler_sum.
by move=> a _ /=; apply/ler_norm_add.
qed.

(* -------------------------------------------------------------------- *)
lemma summable_big ['a 'b] (F : 'a -> 'b -> real) (s : 'b list) :
     (forall y, y \in s => summable (fun x => F x y))
  => summable (fun x => big predT (F x) s).
proof.
elim: s => [|y s ih] sm; first by apply: (eqL_summable _ summable0).
have sm1: summable (fun x => F x y).
+ by apply: sm; rewrite in_cons.
have sm2: summable (fun x => big predT (F x) s).
+ by apply: ih => z z_in_s; rewrite &(sm) in_cons z_in_s.
apply: (eqL_summable _ (summableD sm1 sm2)) => /=.
by move=> x; rewrite big_cons.
qed.

(* -------------------------------------------------------------------- *)
lemma summableZ (s : 'a -> real) (c : real) :
  summable s => summable (fun x => c * s x).
proof.
case=> M h; exists (`|c| * M) => J /h leM.
rewrite -(@eq_bigr _ (fun x => `|c| * `|s x|)) /=.
+ by move=> x _; rewrite normrM.
by rewrite -mulr_sumr ler_wpmul2l 1:normr_ge0.
qed.

lemma summableN (s : 'a -> real) : 
  summable s => summable (fun x => - s x).
proof.  
by move/summableZ/(_ (-1%r)); apply eq_summable => x; rewrite /= mulN1r. 
qed.

(* -------------------------------------------------------------------- *)
lemma summableZ_iff (s : 'a -> real) (c : real) : c <> 0%r =>
  summable s <=> summable (fun x => c * s x).
proof.
move=> nz_c; split; first by apply/summableZ.
move/(@summableZ _ (inv c)); apply/eq_summable => /= x.
by rewrite mulrAC divff.
qed.

(* -------------------------------------------------------------------- *)
lemma summableM_prod_dep ['a 'b] f g:
     summable<:'a> f
  => (exists Mg, forall a J, uniq J => big predT ("`|_|"%Real \o g a) J <= Mg)
  => summable (fun (ab : 'a * 'b) => f ab.`1 * g ab.`1 ab.`2).
proof.
case=> [Mf smf] [Mg smg]; exists (Mf * Mg) => J uqJ.
pose J1 := undup (unzip1 J).
pose F (ab : 'a * 'b) := `|f ab.`1| * `|g ab.`1 ab.`2|.
rewrite (@eq_bigr _ _ F) /= => [ab _|]; 1: by rewrite normrM.
rewrite /F (@sum_pair_dep ("`|_|"%Real \o f) ("`|_|"%Real \o2 g)) //=.
apply: (@ler_trans (big predT (fun i => `|f i| * Mg) J1)); last first.
+ rewrite -mulr_suml ler_wpmul2r; 1: by apply: (@smg witness [] _).
  by apply/smf/undup_uniq.
apply: ler_sum => /= a _; rewrite ler_wpmul2l 1:normr_ge0.
pose G (b : 'b) := `|g a b|.
rewrite big_filter (@eq_bigr _ _ (G \o snd)) => [[a' b] /= ->>//|].
rewrite -big_filter -(@big_map snd predT) &(smg).
apply/map_inj_in_uniq;  last by apply: filter_uniq.
by case=> [a1 b1] [a2 b2]; do 2! (move=> /mem_filter/= [->> _]) => ->.
qed.

(* -------------------------------------------------------------------- *)
lemma summableM_prod ['a 'b] f g:
     summable<:'a> f
  => summable<:'b> g
  => summable (fun (ab : 'a * 'b) => f ab.`1 * g ab.`2).
proof. by move=> smf smg; apply: (@summableM_prod_dep f (fun _ => g)). qed.

(* -------------------------------------------------------------------- *)
op pos (s : 'a -> real) = fun i => if s i < 0%r then 0%r else `|s i|.
op neg (s : 'a -> real) = fun i => if 0%r < s i then 0%r else `|s i|.

lemma pos_neg_id (s : 'a -> real) x: s x = pos s x - neg s x.
proof.
rewrite /pos /neg; case: (s x = 0%r) => [->//=|].
rewrite ltrNge ler_eqVlt (@eq_sym 0%r) => ^ + -> /=.
rewrite eqr_le andabP negb_and -!ltrNge => -[^h ->/=|].
+ by rewrite gtr0_norm.
+ by move/ltrW => ^h /lerNgt -> /=; rewrite ler0_norm.
qed.

lemma pos_neg_abs ['a] f (x : 'a) : pos f x + neg f x = `|f x|.
proof.
rewrite /pos /neg ltrNge ler_eqVlt (@eq_sym 0%r); case: (f x = 0%r) => //=.
- by move=> -> /=; rewrite normr0. - by move=> _; case: (0%r < f x).
qed.

lemma posN (s : 'a -> real) x: pos (fun x => -s x) x = neg s x.
proof. by rewrite /pos /neg /= normrN oppr_lt0. qed.

lemma negN (s : 'a -> real) x: neg (fun x => -s x) x = pos s x.
proof. by rewrite /pos /neg /= normrN oppr_gt0. qed.

lemma pos_ge0 (s : 'a -> real) x: 0%r <= pos s x.
proof. by rewrite /pos; case: (s x < _)=> //=; rewrite normr_ge0. qed.

lemma neg_ge0 (s : 'a -> real) x: 0%r <= neg s x.
proof. by rewrite -posN pos_ge0. qed.

lemma pos_id (s : 'a -> real) : (forall x, 0%r <= s x) => pos s = s.
proof.
move=> ge0_s @/pos; apply/fun_ext => a /=.
by rewrite ltrNge ge0_s /= ger0_norm // ge0_s.
qed.

lemma pos_ger (s : 'a -> real) x: s x <= pos s x.
proof. by rewrite /pos; case: (s x < 0%r)=> [/ltrW|_] //; apply/ler_norm. qed.

lemma neg_ler (s : 'a -> real) x: -neg s x <= s x.
proof. by rewrite -posN ler_oppl pos_ger. qed.

lemma abs_pos_ler (s : 'a -> real) x: `|pos s x| <= `|s x|.
proof.
rewrite /pos; case: (s x < 0%r); 1: by rewrite normr0 normr_ge0.
by move=> _; rewrite normr_id.
qed.

lemma abs_neg_ler (s : 'a -> real) x: `|neg s x| <= `|s x|.
proof. by rewrite -posN -(@normrN (s x)); apply/abs_pos_ler. qed.

lemma ler_pos (s1 s2 : 'a -> real):
  (forall x, s1 x <= s2 x) => forall x, pos s1 x <= pos s2 x.
proof.
move=> le_s12 x @{1}/pos; case: (s1 x < 0%r); 1: by rewrite pos_ge0.
move/lerNgt=> ^ge0_s1x /ger0_norm -> @/pos; rewrite ltrNge.
have ge0_s2x: 0%r <= s2 x by apply/(ler_trans (s1 x))/le_s12.
by rewrite ge0_s2x /= ger0_norm //; apply/le_s12.
qed.

lemma ler_neg (s1 s2 : 'a -> real):
  (forall x, s1 x <= s2 x) => forall x, neg s2 x <= neg s1 x.
proof.
move=> le_s12 x; rewrite -!posN; apply/ler_pos=> y /=.
by rewrite ler_oppr opprK le_s12.
qed.

(* -------------------------------------------------------------------- *)
lemma summable_pos (s : 'a -> real) : summable s => summable (pos s).
proof.
case=> M leM; exists M=> J /leM; (pose F := big _ _ _) => le.
by apply(ler_trans F)=> // @/F; apply/ler_sum=> a _; apply/abs_pos_ler.
qed.

lemma summable_neg (s : 'a -> real) : summable s => summable (neg s).
proof.
case=> M leM; exists M=> J /leM; (pose F := big _ _ _) => le.
by apply(ler_trans F)=> // @/F; apply/ler_sum=> a _; apply/abs_neg_ler.
qed.

(* -------------------------------------------------------------------- *)
lemma summable_has_lub (s : 'a -> real) :
  summable s => has_lub (fun M =>
    exists J, uniq J /\ M = big predT (fun x => `|s x|) J).
proof.
case=> M hM; split; first by exists 0%r []; rewrite big_nil.
by exists M => x [J [uqJ ->]]; apply/hM.
qed.

(* -------------------------------------------------------------------- *)
op psum_pred (s : 'a -> real) =
  fun M => exists J, uniq J /\ M = big predT (fun x => `|s x|) J.

lemma nz_psum_pred (s : 'a -> real) : nonempty (psum_pred s).
proof. by exists 0%r; exists []. qed.

hint exact : nz_psum_pred.

(* -------------------------------------------------------------------- *)
op psum (s : 'a -> real) =
  lub (psum_pred s).

op sum (s : 'a -> real) =
  if summable s then psum (pos s) - psum (neg s) else 0%r.

(* -------------------------------------------------------------------- *)
lemma sum_sbl (s : 'a -> real) : summable s =>
  sum s = psum (pos s) - psum (neg s).
proof. by move=> @/sum ->. qed.

(* -------------------------------------------------------------------- *)
lemma sum_Nsbl (s : 'a -> real) : !summable s => sum s = 0%r.
proof. by move=> @/sum ->. qed.

(* -------------------------------------------------------------------- *)
lemma psum_eq0P (s : 'a -> real) : summable s =>
  (psum s = 0%r) <=> (forall x, s x = 0%r).
proof.
move=> /summable_has_lub sms; split.
+ apply: contraLR => /negb_forall /= [a nz_sa]; rewrite &(gtr_eqF).
  apply: (@ltr_le_trans `|s a|).
    by rewrite ltr_neqAle eq_sym normr0P nz_sa normr_ge0.
  by apply: lub_upper_bound => //; exists [a] => //=; rewrite big_seq1.
+ move=> s_eq0; rewrite eqr_le; split => [|_]; last first.
    by apply: lub_upper_bound => //; exists [].
  apply: lub_le_ub => // a [J [uqJ ->]]; rewrite ler_eqVlt; left.
  by apply: big1 => {a} a _ /=; rewrite normr0P s_eq0.
qed.

(* -------------------------------------------------------------------- *)
lemma ge0_psum ['a] (s : 'a -> real) : summable s => 0%r <= psum s.
proof.
move=> sms; apply: lub_upper_bound; last by exists [].
by apply: summable_has_lub.
qed.

(* -------------------------------------------------------------------- *)
lemma eq_psum ['a] (s1 s2 : 'a -> real) :
  (forall x, `|s1 x| = `|s2 x|) => psum s1 = psum s2.
proof.
move=> eq; apply: eq_lub => x; split; case=> J [uqJ ->];
  by exists J; split=> //; apply: eq_bigr => /= i _; rewrite eq.
qed.

(* -------------------------------------------------------------------- *)
lemma psum_norm ['a] (s : 'a -> real) :
  psum (fun x => `|s x|) = psum s.
proof. by apply: eq_psum=> a /=; rewrite normr_id. qed.

(* -------------------------------------------------------------------- *)
lemma psum_sum s : summable<:'a> s => psum s = sum (fun x => `|s x|).
proof.
move=> sms; rewrite /sum summable_norm //=.
rewrite pos_id /=; first by move=> a; apply: normr_ge0.
rewrite psum_norm -{1}(@subr0 (psum s)); do 2! congr; apply/eq_sym.
apply: psum_eq0P; first by apply/summable_neg/summable_norm.
move=> a @/neg; case: (0%r < `|s a|) => //.
by rewrite ltrNge /= normr_le0 => ->.
qed.

(* -------------------------------------------------------------------- *)
lemma summable_pos_cnvto s :
  forall (J : int -> 'a option) (p : 'a -> bool),
       enumerate J p
    => support s <= p
    => summable s
    => RealSeq.convergeto
         (fun n => big predT (fun x => `|s x|) (pmap J (range 0 n)))
         (psum s).
proof.
move=> J p enm sm sbl; pose u n := big predT _ (pmap J (range 0 n)).
have uqJ: forall n, uniq (pmap J (range 0 n)).
+ move=> n; rewrite pmap_inj_in_uniq ?range_uniq //.
  by move=> x y v _ _; case: enm => + _; apply.
have mono_u: forall n1 n2, (0 <= n1 <= n2)%Int => u n1 <= u n2.
+ move=> n1 n2 len; rewrite /u (@range_cat n1 _ n2); 1..2: by case: len.
  by rewrite pmap_cat big_cat ler_addl sumr_ge0 => x /= _; apply/normr_ge0.
case: (sbl) => M sblM; have := cnvto_lub_bmono_from _ M 0 mono_u _.
+ by move=> n ge0_n; apply/sblM/uqJ.
pose l := lub _; suff ->//: l = psum s; rewrite eqr_le; split.
+ apply/ler_lub => /=; first last.
  * by apply/summable_has_lub.
  * by exists 0%r 0 => /= @/u; rewrite range_geq.
  move=> x [n [ge0_n <-]]; exists (u n) => /=.
  by exists (pmap J (range 0 n)); rewrite uqJ.
move=> _; apply/ler_lub => /=; first last.
+ split; first by exists 0%r 0; rewrite /u range_geq.
  by exists M => x [n [ge0_n <-]]; apply/sblM/uqJ.
+ by exists 0%r [].
have: exists f, forall x,
  0 <= f x /\ (s x <> 0%r => J (f x) = Some x).
+ pose P x i := 0 <= i /\ J i = Some x.
  exists (fun x => choiceb (P x) 0) => x /=; split.
  * case: (exists i, P x i); first by case/(@choicebP (P x) 0).
    by rewrite negb_exists /= => /@choiceb_dfl ->.
  move=> nz_sx; have: exists i, P x i.
  * case: enm => _ /(_ x _); first by apply/sm.
    by case=> i [ge0_i @/P <-]; exists i.
  by move/(@choicebP _ 0) => /= [_ <-].
case=> f fE x [K [uqK ->]]; pose N := 1 + BIA.big predT f K.
exists (u N); split; first exists N => /=.
+ by rewrite addr_ge0 // Bigint.sumr_ge0 => y _; case: (fE y).
rewrite /u (@bigID _ _ (support s)) addrC big1 /=.
+ by move=> i [_ @/predC @/support] /= ->; rewrite normr0.
have ->: predI predT (support s) = support s by apply/fun_ext.
rewrite -big_filter; pose P x := ! x \in (filter (support s) K).
pose F1 := filter _ _; pose F2 := filter P (pmap J (range 0 N)).
have: perm_eq (F1 ++ F2) (pmap J (range 0 N)).
+ apply/uniq_perm_eq; try apply/uqJ.
  * apply/cat_uniq; rewrite !filter_uniq //= ?uqJ.
    apply/negP=> /hasP[y]; rewrite !mem_filter.
    by case=> />; rewrite /P mem_filter => ->.
  move=> y; rewrite mem_cat; case: (y \in F2) => /=.
  * by rewrite mem_filter.
  move=> yF2; split.
  * rewrite mem_filter => -[sy yK]; case: (fE y).
    move=> ge0_fy /(_ sy) Jfy; apply/pmapP.
    exists (f y); rewrite Jfy /= mem_range ge0_fy /= /N.
    rewrite addrC ltzS (@BIA.bigD1 _ _ y) // ler_addl.
    by apply/Bigint.sumr_ge0=> z _; case: (fE z).
  * rewrite pmap_map => /mapP[v]; rewrite !mem_filter /predC1 => />.
    case v yF2 => @/oget //= v' />. 
    rewrite mem_filter /P negb_and /= mem_filter => -[//|].
    move=> h1 h2; suff //: false; move: h2 h1 => /= h.
    rewrite pmap_map; apply/mapP; exists (Some v').
    by rewrite mem_filter.
move/eq_big_perm=> <-; rewrite big_cat ler_addl.
by apply/sumr_ge0=> y /= _; apply/normr_ge0.
qed.

(* -------------------------------------------------------------------- *)
lemma summable_cnvto s :
  forall (J : int -> 'a option) (p : 'a -> bool),
       enumerate J p
    => support s <= p
    => summable s
    => RealSeq.convergeto (fun n => big predT s (pmap J (range 0 n))) (sum s).
proof.
move=> J p enm sm sbl; rewrite /sum sbl /=.
pose G f n := big predT f (pmap J (range 0 n)).
rewrite -/(G s); have ->: G s = fun n =>
  G (fun x => `|pos s x|) n - G (fun x => `|neg s x|) n.
+ apply/fun_ext=> i @/G; rewrite sumrB; apply/eq_bigr.
  by move=> x _ /=; rewrite !ger0_norm ?(pos_ge0, neg_ge0) pos_neg_id.
apply/cnvtoB; apply/(@summable_pos_cnvto _ _ p) => //.
+ move=> x @/support @/pos; case: (s x < 0%r) => //.
  by move=> _; rewrite normr0P &(sm).
+ by apply/summable_pos.
+ move=> x @/support @/neg; case: (0%r < s x) => //.
  by move=> _; rewrite normr0P &(sm).
+ by apply/summable_neg.
qed.

(* -------------------------------------------------------------------- *)
lemma summable_cnv s :
  forall (J : int -> 'a option) (p : 'a -> bool),
       enumerate J p
    => support s <= p
    => summable s
    => RealSeq.converge (fun n => big predT s (pmap J (range 0 n))).
proof.
by move=> J P enm sm sbl; have /cnvP := summable_cnvto _ _ _ enm sm sbl.
qed.

(* -------------------------------------------------------------------- *)
lemma sumEw (s : 'a -> real) :
  forall (J : int -> 'a option) (p : 'a -> bool),
       enumerate J p
    => support s <= p
    => summable s
    => sum s = lim (fun n => big predT s (pmap J (range 0 n))).
proof.
by move=> J p enm le sm; have /lim_cnvto <- := summable_cnvto _ _ _ enm le sm.
qed.

(* -------------------------------------------------------------------- *)
lemma sumE (s : 'a -> real) :
  forall (J : int -> 'a option),
       enumerate J (support s)
    => summable s
    => sum s = lim (fun n => big predT s (pmap J (range 0 n))).
proof. by move=> J /(@sumEw s J (support s)); apply. qed.

(* -------------------------------------------------------------------- *)
lemma sumEc (s : 'a -> real) : summable s => sum s =
  lim (fun n => big predT s (pmap (cenum (support s)) (range 0 n))).
proof. by move=> ^sns; apply/sumE/enum_cenum/sbl_countable. qed.

(* -------------------------------------------------------------------- *)
lemma sum_to_enum (s : 'a -> real) : summable s =>
  exists (J : int -> 'a option), enumerate J (support s).
proof.
by move/sbl_countable/countableP=> [C] /= [inj_C suppC]; exists C; split.
qed.

(* -------------------------------------------------------------------- *)
lemma sumE_fin ['a] (s : 'a -> real) (J : 'a list) :
     uniq J
  => (forall x, s x <> 0%r => mem J x)
  => sum s = big predT s J.
proof.
move=> uqJ sJ; rewrite (@sumE _ (nth None (map Some J))); 1: split.
+ move=> i j x /=; pose n := size J; case: (0 <= i < n); last first.
    by move=> Nrg_i; rewrite nth_out ?size_map.
  case: (0 <= j < n); last by move=> Nrg_j _ _; rewrite nth_out ?size_map.
  move=> lt_jn lt_in; rewrite !(@nth_map x) //= => {2}<-.
  by move/(congr1 (fun x => index x J))=> /=; rewrite !index_uniq.
+ move=> x /sJ sx; exists (index x J); rewrite ?index_ge0 /=.
  by rewrite (@nth_map x) /= 1:index_ge0 1:index_mem // nth_index.
+ exists (big predT (fun x => `|s x|) (filter (fun x => s x <> 0%r) J))=> J' uniq_J'.
  rewrite -(eq_big_perm (:@perm_filterC (fun x => s x <> 0%r) J')).
  rewrite big_cat (@big1_seq _ _ (filter (fun (x : 'a) => s x = 0%r) J')) /=.
  * by move=> x @/predT; rewrite mem_filter /= =>- [] ->.
  rewrite -(eq_big_perm (:@perm_filterC (fun x => mem J' x) (filter _ J))).
  rewrite -!filter_predI /predC /predI /= big_cat; apply/ler_paddr.
  * by apply/sumr_ge0=> a //=; rewrite normr_ge0.
  rewrite -(@eq_big_perm _ _ (filter (fun x => mem J' x /\ s x <> 0%r) J)).
  * apply/uniq_perm_eq=> [| |x]; 1,2: exact/filter_uniq.
    by rewrite !mem_filter /=; split=> //= -[] ^/sJ.
  exact/lerr_eq.
apply/(@limC_eq_from (size J)) => n ge_Jn /=.
rewrite (@range_cat (size J)) 1:size_ge0 // pmap_cat big_cat.
rewrite addrC -(@eq_in_pmap (fun i => None)) ?pmap_none ?big_nil /=.
  by move=> x /mem_range [le_Jx lt_xn]; rewrite nth_default ?size_map.
congr; pose F := fun (i : int) => Some (nth witness J i).
rewrite -(@eq_in_pmap F) /F 2:pmap_some 2:map_nth_range //.
by move=> x /mem_range lt_xJ /=; rewrite (@nth_map witness).
qed.

(* -------------------------------------------------------------------- *)
lemma fin_sum_cond (P : 't -> bool) f :
  is_finite P =>
  sum (fun z => if P z then f z else 0%r) = big predT f (to_seq P).
proof.
move=> P_finite; rewrite (@sumE_fin _ (to_seq P)) /= ?uniq_to_seq //.
- smt(mem_to_seq).
by apply eq_big_seq => x; smt(mem_to_seq).
qed.

lemma fin_sum_const (P : 't -> bool) (v : real) :
  is_finite P =>
  sum (fun z => if P z then v else 0%r) = (size (to_seq P))%r * v.
proof.
move=> P_finite.
by rewrite fin_sum_cond // sumr_const RField.intmulr count_predT RField.mulrC.
qed.

lemma fin_sum_type (s : 'a -> real) :
  is_finite predT<:'a> => 
  sum s = big predT s (to_seq predT<:'a>).
proof.
move=> fint; rewrite &(sumE_fin) 1:uniq_to_seq.
by move=> x _; rewrite mem_to_seq. 
qed.

(* -------------------------------------------------------------------- *)
lemma sum0 ['a]: sum<:'a> (fun _ => 0%r) = 0%r.
proof. by rewrite (@sumE_fin _ []). qed.

lemma sum_bool (f : bool -> real):
  sum f = f true + f false.
proof. by rewrite (@sumE_fin _ [true; false]) //= => -[]. qed.

(* -------------------------------------------------------------------- *)
lemma lerfin_sum (s : 'a -> real) M:
     summable s
  => (forall J, uniq J => big predT s J <= M)
  => sum s <= M.
proof.
move=> ^/sum_to_enum[J en_sJ] sm_s le_sM.
have := summable_cnvto _ _ _ en_sJ _ sm_s => //.
(pose F n := big predT s (pmap J (range 0 n))) => cnv.
apply: (@le_cnvto_from F (fun _ => M) _ _ _ cnv) => /=; last first.
+ by apply/cnvtoC.
+ by exists 0 => n _; apply/le_sM/(enum_uniq_pmap_range _ en_sJ).
qed.

(* -------------------------------------------------------------------- *)
lemma ler_psum_reindex ['a 'b] h s1 s2 :
     injective h
  => (forall x, `|s1 x| <= `|s2 (h x)|)%Real
  => summable s2 => psum<:'a> s1 <= psum<:'b> s2.
proof.
move=> inj_h le_s12 ^sbl_s2 [M2 bs2]; have ^sbl_s1 [M1 bs1]: summable s1.
+ exists M2 => J uqJ; pose K := map h J; have: uniq K.
  * by apply: map_inj_in_uniq; first by move=> x y _ _ /inj_h.
  move/bs2; (pose F := big _ _ _) => leFM.
  rewrite (ler_trans F) // /F big_map; apply/ler_sum.
  by move=> a _ /=; apply/le_s12.
apply/ler_lub; first last; first split.
+ by exists 0%r []=> /=; apply/eq_sym/(@big_nil _ _).
+ by exists M2=> x [J] [+ ->] - /bs2.
+ by exists 0%r []=> /=; apply/eq_sym/(@big_nil _ _).
move=> x [J] [uqJ ->] /=; exists (big predT (fun x => `|s2 x|) (map h J)).
split; [exists (map h J) => /= | by rewrite big_map &(ler_sum)].
by apply: map_inj_in_uniq; first by move=> 4? /inj_h.
qed.

(* -------------------------------------------------------------------- *)
lemma ler_psum (s1 s2 : 'a -> real) :
     (forall x, `|s1 x| <= `|s2 x|)
  => summable s2 => psum s1 <= psum s2.
proof. by apply: ler_psum_reindex. qed.

(* -------------------------------------------------------------------- *)
lemma ler_sum (s1 s2 : 'a -> real) :
     (forall x, s1 x <= s2 x)
  => summable s1 => summable s2
  => sum s1 <= sum s2.
proof.
move=> le_s12 sbl1 sbl2; rewrite !sum_sbl // ler_sub.
  apply/ler_psum/summable_pos/sbl2=> x.
  by rewrite !ger0_norm ?pos_ge0 ler_pos.
apply/ler_psum/summable_neg/sbl1=> x.
by rewrite !ger0_norm ?neg_ge0 ler_neg.
qed.

(* -------------------------------------------------------------------- *)
lemma ge0_sum (s : 'a -> real) :
  (forall x, 0%r <= s x) => 0%r <= sum s.
proof.
case: (summable s) => [sbl_s|/sum_Nsbl ->//].
by move=> ge0_s; rewrite -sum0<:'a> ler_sum //= &(summable0).
qed.

(* -------------------------------------------------------------------- *)
lemma eq_summable_norm ['a] (f g : 'a -> real) :
  (forall x, `|f x| = `|g x|) => summable f <=> summable g.
proof. by move=> eq_fg; split=> /summable_le; apply=> x; rewrite eq_fg. qed.

(* -------------------------------------------------------------------- *)
lemma summable_le_pos (s1 s2 : 'a -> real) :
     summable s2
  => (forall x, 0%r <= s1 x <= s2 x)
  => summable s1.
proof.
move=> sbl_s2 h; apply/(summable_le _ sbl_s2) => x.
by have {h} [h1 h2] := h x; rewrite !ger0_norm // (ler_trans _ h1 h2).
qed.

lemma ler_sum_pos ['a] (s1 s2 : 'a -> real) : 
  (forall (x : 'a), 0%r <= s1 x <= s2 x) => 
  summable s2 => sum s1 <= sum s2.
proof.
move => sbl_s2 sum_s2; apply: ler_sum => //; 1: by move => x; case (sbl_s2 x).
by apply (summable_le_pos _ _ sbl_s2).
qed.

(* -------------------------------------------------------------------- *)
lemma summable_cond (s : 'a -> real) (p : 'a -> bool) :
  summable s => summable (fun x => if p x then s x else 0%r).
proof.
move=> sbl_s; apply/(summable_le _ sbl_s) => x /=.
by case: (p x) => // _; rewrite normr0 normr_ge0.
qed.

(* --------------------------------------------------------------------- *)
lemma summable_cond_fin ['a] (s : 'a -> real) (p : 'a -> bool) :
  is_finite p => summable (fun x => if p x then s x else 0%r).
proof.
move=> fin_p; apply: (@summable_fin _ (to_seq p)) => /= x.
by case: (p x) => // px _; rewrite mem_to_seq.
qed.

(* -------------------------------------------------------------------- *)
lemma eq_sum (s1 s2 : 'a -> real) :
  (forall x, s1 x = s2 x) => sum s1 = sum s2.
proof. by move/fun_ext=> ->. qed.

(* -------------------------------------------------------------------- *)
lemma sum_norm s :
  (forall x, 0%r <= s x) => sum<:'a> (fun x => `|s x|) = sum s.
proof.
by move=> ge0_s; apply: eq_sum => a /=; rewrite ger0_norm // &(ge0_s).
qed.

(* -------------------------------------------------------------------- *)
lemma sum0_eq (s : 'a -> real) :
  (forall x, s x = 0%r) => sum s = 0%r.
proof. by move=> z_s; rewrite -sum0<:'a>; apply/eq_sum. qed.

(* -------------------------------------------------------------------- *)
lemma sumD s1 s2 : summable s1 => summable s2 =>
  sum<:'a> (fun x => s1 x + s2 x) = sum s1 + sum s2.
proof.
move=> cv1 cv2; pose s := fun x => s1 x + s2 x.
have cvs: summable s by move=> @/s; apply/summableD.
pose E x := support s x \/ support s1 x \/ support s2 x.
have cntE: countable E by do! apply/countableU; apply sbl_countable.
pose J := cenum E; have enmJ: enumerate J E by apply/enum_cenum.
have h1: support s1 <= E by move=> x @/E ->.
have h2: support s2 <= E by move=> x @/E ->.
rewrite !(@sumEw _ J E) //; first by move=> x @/E ->.
rewrite -limD 1..2:&(summable_cnv _ enmJ) ~-1://.
by apply/(@lim_eq 0)=> n ge0_n /=; rewrite big_split.
qed.

(* -------------------------------------------------------------------- *)
lemma sumZ (s : 'a -> real) c : sum (fun x => c * s x) = c * sum s.
proof.
case: (c = 0%r) => [->/=|]; first by rewrite sum0_eq.
move=> nz_c; case: (summable s); last first.
+ by move=> h; rewrite !sum_Nsbl // -summableZ_iff.
move=> sbl_s; have sbl_cs := summableZ _ c sbl_s.
have /sum_to_enum[J cJ] := sbl_s; rewrite !(@sumE _ J) //.
+ apply/(@eq_enumerate (support s)) => //= y.
  by rewrite /support mulf_eq0 nz_c.
by rewrite -limZ; apply/(@lim_eq 0) => n /= _; rewrite mulr_sumr.
qed.

(* -------------------------------------------------------------------- *)
lemma sumZr (s : 'a -> real) c : sum (fun x => s x * c) = sum s * c.
proof. by rewrite mulrC -sumZ; apply/eq_sum=> x /=; apply/mulrC. qed.

(* -------------------------------------------------------------------- *)
lemma sumN (s : 'a -> real) : sum (fun x => - s x) = - sum s.
proof. by rewrite -mulN1r -sumZ &(eq_sum) /#. qed.

(* -------------------------------------------------------------------- *)
lemma sumB (s1 s2 : 'a -> real) :
  summable s1 => summable s2 => sum (fun x => s1 x - s2 x) = sum s1 - sum s2.
proof. by move=> sm1 sm2; rewrite sumD // 1:&(summableN) // sumN. qed.

(* -------------------------------------------------------------------- *)
lemma le0_sum (s : 'a -> real) : 
  (forall x, s x <= 0%r) => sum s <= 0%r.
proof. 
by move=> le0_s; rewrite -(add0r (sum s)) -ler_subr_addr /= -sumN &(ge0_sum) /#.
qed.

(* -------------------------------------------------------------------- *)
lemma sum_split ['a] (s : 'a -> real) p : summable s => sum s =
    sum (fun x => if  p x then s x else 0%r)
  + sum (fun x => if !p x then s x else 0%r).
proof.
move=> sms; rewrite -sumD 1?summable_cond // &(eq_sum) /=.
by move=> x; case: (p x).
qed.

(* -------------------------------------------------------------------- *)
lemma sumD1 ['a] (s : 'a -> real) x0 : summable s => sum s =
  s x0 + sum (fun x => if x <> x0 then s x else 0%r).
proof.
move=> sms; rewrite (@sum_split s (pred1 x0)) //=; congr=> //.
rewrite (@sumE_fin _ [x0]) //= 1?big_seq1 //.
by move=> @/pred1 x; case: (x = x0).
qed.

(* -------------------------------------------------------------------- *)
lemma sum_split_norm (s : 'a -> real) : summable s => 
    sum (fun x => `|s x|) = 
    sum (fun x => if 0%r <= s x then s x else 0%r) - 
    sum (fun x => if ! 0%r <= s x then s x else 0%r).
proof.
move=> sum_s; rewrite (@sum_split _ (fun x => 0%r <= s x)) /=.
  exact summable_norm.
by congr; [|rewrite -sumN]; apply eq_sum => x /=; smt().
qed.

(* -------------------------------------------------------------------- *)
lemma sum_split_dist (f g : 'a -> real) : summable f => summable g => 
  sum (fun x => `|f x - g x|) = 
  sum (fun x => if g x <= f x then f x - g x else 0%r) - 
  sum (fun x => if ! g x <= f x then f x - g x else 0%r).
proof.
move=> sum_f sum_g; rewrite sum_split_norm /=.
 by  apply summableD => //; apply/summableN.
by congr;[|congr]; apply eq_sum => x /= /#.
qed.

(* -------------------------------------------------------------------- *)
lemma sum_big ['a 'b] (F : 'a -> 'b -> real) (s : 'b list) :
     (forall y, y \in s => summable (fun x => F x y))
  =>   sum (fun x => big predT (F x) s)
     = big predT (fun y => sum (fun x => F x y)) s.
proof.
elim: s => [|y s ih] sm; first by rewrite big_nil sum0.
rewrite big_cons /predT /= -ih -?sumD /=.
+ by move=> z z_in_s; rewrite &(sm) in_cons z_in_s.
+ by rewrite &(sm) in_cons.
+ by apply: summable_big => z z_in_s; apply: sm; rewrite in_cons z_in_s.
by apply: eq_sum => /= x; rewrite big_cons.
qed.

(* -------------------------------------------------------------------- *)
lemma psum_big ['a 'b] (F : 'a -> 'b -> real) (s : 'b list) :
     (forall y, y \in s => summable (fun x => F x y))
  =>   psum (fun x => big predT (fun y => `|F x y|) s)
     = big predT (fun y => psum (fun x => F x y)) s.
proof.
move=> sms; rewrite psum_sum.
+ by apply/summable_big=> b bs /=; apply/summable_norm/sms.
rewrite sum_norm /= -1:sum_big.
+ by move=> a; apply: sumr_ge0 => /= b _; apply: normr_ge0.
+ by move=> b bs /=; apply/summable_norm/sms.
by rewrite !big_seq &(eq_bigr) => /= b bs; rewrite psum_sum 1:&(sms).
qed.

(* -------------------------------------------------------------------- *)
lemma ler_psum_lub ['a] (s : 'a -> real) z :
     (forall J, uniq J => big predT (fun x => `|s x|) J <= z)
  => psum s <= z.
proof.
move=> le; have sm: summable s by exists z.
apply: lub_le_ub; first by apply: summable_has_lub.
by move=> x [J [uqJ ->]]; apply: le.
qed.

(* -------------------------------------------------------------------- *)
lemma psumB (s1 s2 : 'a -> _) : summable s1 => summable s2 =>
  psum s1 - psum s2 = sum (fun x => `|s1 x| - `|s2 x|).
proof.
by move=> sm1 sm2; rewrite !psum_sum // -sumB // &(summable_norm).
qed.

(* -------------------------------------------------------------------- *)
lemma ler_big_psum ['a] s J : summable<:'a> s => uniq J =>
  big predT (fun x => `|s x|) J <= psum s.
proof.
move=> sms uqJ @/psum; apply: lub_upper_bound.
  by apply: summable_has_lub. by exists J.
qed.

lemma ler_big_sum (s : 'a -> real) (J : 'a list) : 
  (forall x, 0%r <= s x) => uniq J => summable s => 
  big predT s J <= sum s.
proof.
move => *; rewrite (@sum_split _ (mem J)) //.
apply ler_paddr; 1: smt(ge0_sum). 
by rewrite (@sumE_fin _ J) //= 1:/# -big_mkcond -big_seq. 
qed.

(* -------------------------------------------------------------------- *)
lemma summable_psum_partition ['a 'b] (f : 'a -> 'b) s : summable<:'a> s =>
  forall J, uniq J =>
    big predT (fun b => psum (fun a => if b = f a then s a else 0%r)) J <= psum s.
proof.
move=> sms J uqJ; rewrite -psum_big /=.
  by move=> b _; apply/summable_cond.
apply: ler_psum => //= a; case: (f a \in J) => faJ; last first.
  rewrite big_seq big1 /=; last by rewrite normr0 normr_ge0.
  by move=> b bJ; case: (b = f a).
rewrite (@bigD1 _ _ (f a)) //= big1 /= //.
  by move=> ? -> /=; rewrite normr0.
  by rewrite normr_id.
qed.

(* -------------------------------------------------------------------- *)
lemma psum_partition ['a 'b] (f : 'a -> 'b) s : summable s =>
  psum s = psum (fun y => psum (fun x => if y = f x then s x else 0%r)).
proof.
move=> sms; pose v y x := if y = f x then `|s x| else 0%r.
have: forall J, uniq J => big predT (fun y => psum (v y)) J <= psum s.
+ move=> J uqJ; have h := summable_psum_partition f s sms J uqJ.
  rewrite &(ler_trans _ _ h) lerr_eq &(eq_bigr) => b _ /=.
  by apply: eq_psum => a @/v /= /#.
move=> sm; rewrite eqr_le; split => [|_].
+ pose F x y := if y = f x then s x else 0%r.
  pose G y := psum (fun x => F x y).
  apply: ler_psum_lub => J uqJ; pose L := undup (map f J).
  apply: (@ler_trans (big predT (fun y => `|G y|) L)); last first.
    apply/ler_big_psum/undup_uniq => @/G @/F; case: (sms) => M smsM {J L uqJ}.
    exists M => J uqJ; apply/(@ler_trans (psum s))/ler_psum_lub => //.
    apply: (ler_trans _ _ (sm uqJ)); rewrite lerr_eq &(eq_bigr).
    move=> b _ /=; rewrite ger0_norm; 1: by apply/ge0_psum/summable_cond.
    by apply: eq_psum => a /= @/v /#.
  rewrite /G /F (@partition_big f predT predT _ J L) /=.
  - by apply/undup_uniq.
  - by move=> x xJ _ @/L; rewrite mem_undup map_f.
  apply: ler_sum_seq => b bL _ /= @/predT /=; rewrite big_mkcond /=.
  rewrite ger0_norm; first by rewrite ge0_psum summable_cond.
  have smc := summable_cond _ (fun x => b = f x) sms.
  apply: (ler_trans _ _ (ler_big_psum smc uqJ)) => {smc}.
  by rewrite lerr_eq &(eq_bigr) => a /= _ /#.
+ apply: ler_psum_lub => J uqJ; rewrite sumr_norm /=.
  - by move=> ? _; apply/ge0_psum/summable_cond.
  rewrite -psum_big /=.
  - by move=> b _; apply/summable_cond.
  apply: ler_psum => //= a; case: (f a \in J) => faJ; last first.
    rewrite big_seq big1 /=; last by rewrite normr0 normr_ge0.
    by move=> b bJ; case: (b = f a).
  rewrite (@bigD1 _ _ (f a)) //= big1 //=.
  - by move=> ? ->; rewrite normr0.
  - by rewrite normr_id.
qed.

(* -------------------------------------------------------------------- *)
lemma sum_partition ['a 'b] (f : 'a -> 'b) s : summable s =>
  sum s = sum (fun y => sum (fun x => if y = f x then s x else 0%r)).
proof.
move=> sms; rewrite sum_sbl //.
have hp : forall b, summable (fun x => if b = f x then pos s x else 0%r).
+ by move=> b; apply/summable_cond/summable_pos.
have hn : forall b, summable (fun x => if b = f x then neg s x else 0%r).
+ by move=> b; apply/summable_cond/summable_neg.
rewrite (@psum_partition f (pos s)) 1:&summable_pos //.
rewrite (@psum_partition f (neg s)) 1:&summable_neg //.
rewrite psumB /=; last apply: eq_sum => b /=.
+ exists (psum (pos s)) => J uqJ; rewrite sumr_norm /=.
    by move=> b _; apply/ge0_psum/hp.
  by apply: summable_psum_partition => //; apply/summable_pos.
+ exists (psum (neg s)) => J uqJ; rewrite sumr_norm /=.
    by move=> b _; apply/ge0_psum/hn.
  by apply: summable_psum_partition => //; apply/summable_neg.
rewrite ger0_norm; 1: by apply/ge0_psum/hp.
rewrite ger0_norm; 1: by apply/ge0_psum/hn.
by rewrite psumB /=; [apply/hp | apply/hn | apply: eq_sum] => /#.
qed.

(* -------------------------------------------------------------------- *)
lemma norm_sum ['a] (s : 'a -> real) : summable s => `|sum s| <= psum s.
proof.
move=> sms; rewrite psum_sum // ler_norml; split=> [|_]; last first.
- apply: ler_sum => //=; last by apply/summable_norm.
  by move=> a; apply/ler_norm.
rewrite -sumN /=; apply/ler_sum => //=; last first.
- by apply/summableN/summable_norm.
by move=> a; rewrite ler_oppl ler_normr.
qed.

(* -------------------------------------------------------------------- *)
lemma summable_partition ['a 'b] (f : 'a -> 'b) s : summable s =>
  summable (fun y => sum (fun x => if y = f x then s x else 0%r)).
proof.
move=> sms; exists (psum s) => J uqJ.
have h := summable_psum_partition f s sms J uqJ.
apply/(ler_trans _ _ h)/Bigreal.ler_sum => /= b _.
by apply/norm_sum/summable_cond.
qed.

(* -------------------------------------------------------------------- *)
lemma summable_inj (h : 'a -> 'b) (s : 'b -> real) : 
  injective h => summable s => summable (s \o h).
proof.
move => inj_h [M] sum_s; exists M => J uniq_J. 
have R := sum_s (map h J) _.
+ by rewrite map_inj_in_uniq=> // x y _ _ /inj_h.
apply (ler_trans _ _ R) => {R}; rewrite big_map /(\o)/= big_mkcond.
exact Bigreal.ler_sum.
qed.

lemma summable_bij ['a 'b] (h : 'a -> 'b) s :
  bijective h => summable s => summable (s \o h).
proof. move/bij_inj. exact summable_inj. qed.

lemma summableM (s1 s2 : 'a -> real) : 
  summable s1 => summable s2 => summable (fun x => s1 x * s2 x).
proof.
move => sum_s1 sum_s2; have H := summableM_prod _ _ sum_s1 sum_s2.
have := summable_inj (fun x : 'a => (x,x)) _ _ H; 1: by move=> x y [-> _].
by move => sum_s; apply (summable_le _ sum_s).
qed.

lemma summableM_bound (k : real) (s1 s2 : 'a -> real)  : 
  0%r < k => summable s1 => (forall x, `|s2 x| <= k) => 
  summable (fun x => s1 x * s2 x).
proof.
move => k_gt0 [M sum_s1] bound_s2; exists (k * M) => J uniq_J. 
have R := sum_s1 _ uniq_J; rewrite -(@ler_pmul2l k) // in R.
apply (ler_trans _ _ R) => {R}; rewrite mulr_sumr /=.
by apply Bigreal.ler_sum => /= x; rewrite normrM Domain.mulrC ler_wpmul2r /#.
qed.

(* -------------------------------------------------------------------- *)

lemma summable_oapp (s : 'a -> real) x : 
  summable s => summable (oapp s x).
proof.
move/(summable_partition Some); apply (eqL_notin_summable [None]).
by case => //= z; rewrite (@sumE_fin _ [z]) //= => z'; case (z = z'). 
qed.

(* -------------------------------------------------------------------- *)
lemma sum_reindex ['a 'b] (h : 'a -> 'b) s :
  bijective h => summable s => sum (s \o h) = sum s.
proof.
move=> bij_h sms; rewrite sumEc // 1:&(summable_bij) //.
pose J := cenum _; rewrite (@sumEw _ (fun i => omap h (J i)) (support s)) //.
+ have: enumerate (cenum (support (s \o h))) (support (s \o h)).
    by apply/enum_cenum/sbl_countable/summable_bij.
  case=> h1 h2; split => [i j b|b sup_sb]; last first.
  - case: bij_h => hV [canh canhV]; case: (h2 (hV b) _).
      by rewrite /support /(\o) canhV &(sup_sb).
    by move=> i [ge0_i @/J E]; exists i; rewrite ge0_i /= E /= canhV.
  - case: bij_h => hV [canh canhV]; have := h1 i j (hV b).
    rewrite -/(J i) -/(J j); case: (J i) => //; case: (J j) => //.
    move=> a1 a2 /= eq_ij bE1 bE2; apply: eq_ij.
      by rewrite -bE1 canh. by rewrite -bE2 canh.
apply: (@lim_eq 0) => n _ /=; rewrite -(@big_map h predT).
apply: congr_big => //; move: (range _ _) => si.
by elim: si => //= x si ih; case: (J x).
qed.

(* -------------------------------------------------------------------- *)
lemma summable_pair_sum (s : 'a * 'b -> real) :
  summable s => summable (fun x => sum (fun y => s (x, y))).
proof.
move=> sms; have /= := summable_partition fst s sms.
apply: eq_summable=> /= a; pose F (b : 'b) := (a, b).
rewrite (@sum_partition snd) 1:summable_cond //=.
by apply: eq_sum => /= b; rewrite (@sumE_fin _ [(a, b)]) //= /#.
qed.

(* -------------------------------------------------------------------- *)
lemma sum_pair ['a 'b] (s : 'a * 'b -> real) :
  summable s => sum s = sum (fun a => sum (fun b => s (a, b))).
proof.
move=> sms; rewrite (@sum_partition<:'a * 'b, 'a> fst) 1://.
apply: eq_sum => a /=.
rewrite (@sum_partition<:'a * 'b, 'b> snd) 1:&(summable_cond) //=.
apply: eq_sum => b /=.
by rewrite (@sumE_fin _ [(a, b)]) //= /#.
qed.

(* -------------------------------------------------------------------- *)
lemma summable_pswap ['a 'b] (s : 'a * 'b -> real) :
  summable s => summable (s \o pswap).
proof. by apply/summable_bij/bij_pswap. qed.

lemma summable_swap ['a 'b] (fa : 'a -> real) (fb : 'b -> real) (F : 'a -> 'b -> real) :
     (forall x, 0%r <= fa x)
  => (forall y, 0%r <= fb y)
  => (forall x y, 0%r <= F x y)
  => summable (fun y => sum (fun x => fa x * F x y) * fb y)
  => (forall y, fb y <> 0%r => summable (fun x => fa x * F x y))
  => summable (fun x => fa x * sum (fun y => F x y * fb y))
  /\ (forall x, fa x <> 0%r => summable (fun y => F x y * fb y)).
proof.
move=> ge0_fa ge0_fb ge0_F smb subsmb; rewrite andbC &(andaE); split.
- move=> x nz_fax; pose S := fun y => sum (fun x => fa x * F x y) * fb y.
  rewrite (@summableZ_iff _ (fa x)) //; move/summable_le_pos: smb.
  apply => y /=; split.
  - by apply/mulr_ge0/mulr_ge0/ge0_fb/ge0_F/ge0_fa.
  move=> _; case: (fb y = 0%r) => [-> // | nz_fb_y].
  rewrite mulrA; apply: ler_wpmul2r; first exact/ge0_fb.
  have := ler_big_sum (fun x => fa x * F x y) [x] _ _ _ => //=.
  - move=> x'; apply: mulr_ge0; [exact/ge0_fa | exact/ge0_F].
    by apply: subsmb.
move=> subsmb2; pose S := fun y => sum (fun x => fa x * F x y) * fb y.
exists (sum S) => J uqJ. pose G y x := fa x * (F x y * fb y).
have ge0_G: forall x y, 0%r <= G y x.
- by move=> x y; rewrite mulr_ge0 1?ge0_fa mulr_ge0 (ge0_fb, ge0_F).
rewrite (@BRA.eq_bigr _ _ (fun x => sum (fun y => G y x))) /=.
- move=> x _ @/G; rewrite ger0_norm.
  - apply: mulr_ge0; [exact/ge0_fa | apply: ge0_sum => y /=].
    by apply: mulr_ge0; [exact/ge0_F | exact/ge0_fb].
  by rewrite -sumZ /= &(eq_sum) => y /=.
rewrite -sum_big => [y _ @/G|].
- case: (fa y = 0%r) => [-> /=|]; first exact/summable0.
  by move/subsmb2; apply/summableZ.
apply: ler_sum_pos => /= [y|]; [split | exact/smb].
- by rewrite Bigreal.sumr_ge0 => x _ @/G; exact/ge0_G.
move=> _ @/S @/G; case: (fb y = 0%r) => [-> /= | nz_fb_y].
- by rewrite BRA.big1_eq.
rewrite -sumZr -(@BRA.eq_bigr _ (fun x => (fa x * F x y) * fb y)) /=.
- by move=> x _; ring.
rewrite -BRA.mulr_suml sumZr &(ler_wpmul2r) 1:&ge0_fb.
apply: ler_big_sum => //=.
- by move=> x; apply: mulr_ge0; [exact/ge0_fa | exact/ge0_F].
- by apply: subsmb.
qed.

lemma summable_swapR ['a 'b] (fa : 'a -> real) (fb : 'b -> real) (F : 'a -> 'b -> real) :
     (forall x, 0%r <= fa x)
  => (forall y, 0%r <= fb y)
  => (forall x y, 0%r <= F x y)
  => summable (fun x => fa x * sum (fun y => F x y * fb y))
  => (forall x, fa x <> 0%r => summable (fun y => F x y * fb y))
  => summable (fun y => sum (fun x => fa x * F x y) * fb y)
  /\ (forall y, fb y <> 0%r => summable (fun x => fa x * F x y)).
proof.
move=> ge0_fa gr0_fb ge0_F smb subsmb.
have := summable_swap fb fa (fun y x => F x y) _ _ _ _ _ => //=.
- by move=> y x; apply: ge0_F.
- apply: eq_summable smb => x /=; rewrite RField.mulrC.
  by congr; apply: eq_sum => y /=; ring.
- by move=> x /subsmb; apply: eq_summable => y /=; ring.
case=> smb2 subsmb2; split.
- apply: eq_summable smb2 => y /=; rewrite RField.mulrC.
  by congr; apply: eq_sum => x /=; ring.
- by move=> y /subsmb2; apply: eq_summable => x /=; ring.
qed.

lemma pswap_summable (s : 'a * 'b -> real) : 
  summable (s \o pswap) => summable s.
proof. by move=> /summable_pswap; apply eq_summable => -[//]. qed.

lemma sum_swap ['a 'b] (s : 'a * 'b -> real) : summable s =>
  sum (fun a => sum (fun b => s (a, b))) = sum (fun b => sum (fun a => s (a, b))).
proof.
move=> sm_s; rewrite -sum_pair // -(@sum_reindex pswap) //.
+ by apply: bij_pswap. + by rewrite sum_pair // summable_pswap.
qed.

(* the pattern [s a b] seems to be preferrable over the pattern [s(a,b)] *)
lemma sum_swap' (s : 'a -> 'b -> real) :
  summable (fun p : 'a * 'b => s p.`1 p.`2) => 
  sum (fun (a : 'a) => sum (fun (b : 'b) => s a b)) = 
  sum (fun (b : 'b) => sum (fun (a : 'a) => s a b)).
proof. exact (@sum_swap (fun (ab : 'a * 'b) => s ab.`1 ab.`2)). qed.

(* -------------------------------------------------------------------- *)
lemma sump_eq0P (s : 'a -> real) :
     (forall x, 0%r <= s x)
  => summable s
  => (sum s = 0%r <=> forall x, s x = 0%r).
proof.
move=> ge0_s sbl_s; split; last by apply/sum0_eq.
apply: contraLR => /negb_forall [x /= nz_sx].
pose s1 := fun y => if x =  y then s y else 0%r.
pose s2 := fun y => if x <> y then s y else 0%r.
have ->: s = fun x => s1 x + s2 x.
+ by apply/fun_ext=> y @/s1 @/s2; case: (x = y).
rewrite (@sumD s1 s2) 1,2:summable_cond //.
rewrite gtr_eqF // ltr_spaddl; last first.
+ by apply/ge0_sum => @/s2 y; case: (x = y) => //= _; apply/ge0_s.
rewrite (@sumE_fin _ [x]) // => [y @/s1|]; first by case: (x = y).
by rewrite big_seq1 /s1 /= ltr_neqAle eq_sym ge0_s.
qed.

(* -------------------------------------------------------------------- *)
lemma ler_sum_norm (s : 'a -> real) : 
  summable s => sum s <= sum (fun x => `|s x|).
proof.
move => sum_s; apply ler_sum => // => [x|]; 1: exact ler_norm. 
exact summable_norm.
qed.

lemma ler_norm_sum (s : 'a -> real) : 
  summable s => `| sum s | <= sum (fun x => `| s x |).
proof.
move => sum_s; rewrite ler_norml ler_sum_norm //= ler_oppl -sumN. 
apply ler_sum => /=; [smt()| exact summableN| exact summable_norm].
qed.

lemma sum_oapp (s : 'a -> real) x : 
  summable s => sum (oapp s x) = x + sum s.
proof. 
move=> sum_s; rewrite (@sumD1 _ None) ?summable_oapp //=; congr.
rewrite (@sum_partition Some s) // &(eq_sum). 
by case=> /= [|a]; rewrite ?sum0 // (@sumE_fin _ [a]) // /#.
qed.

lemma sumD1_None (s : 'a option -> real) :
  summable s => sum s = s None + sum (s \o Some).
proof.
have E sum_s : s = oapp (s \o Some) (s None) by apply/fun_ext => -[|].
rewrite {1}E sum_oapp //; exact summable_inj.
qed.

(* -------------------------------------------------------------------- *)
lemma prodrDl ['t 'u] (F : 't -> 'u -> real) (r : 't list) (s : 'u list) :
  uniq r => uniq s =>

    BRM.big predT (fun x => big predT (F x) s) r
  = sum (fun sigma => if fixfinfun (mem r) (mem s) sigma then
      BRM.big predT (fun x => F x (sigma x)) r
    else 0%r).
proof.
move=> + uq_s; elim: r => /= [|x r ih [x_notin_r uq_r]].
- rewrite BRM.big_nil (@sumE_fin _ [fun _ => witness]) //=.
  move=> sg; rewrite (@eqL_fixfinfun pred0) //.
  by case _: (fixfinfun _ _ _) => //= /fixfinfun0 /fun_ext + _.
rewrite BRM.big_consT /= ih // => {ih}; pose S := sum _; apply/eq_sym.
pose P (sg : 't -> 'u) := sg x; rewrite (@sum_partition P).
- by apply/summable_cond_fin/finite_fixfinfun; apply/finite_mem.
rewrite (@sumE_fin _ s) //= => [u @/P|].
- apply/contraR => u_notin_s; apply: sum0_eq => /= sg.
  by case: (u = sg x) => // ->>; case _: (fixfinfun _ _ _) => // /(_ x).
rewrite mulr_suml !big_seq &(eq_bigr) /= => u u_in_s @/S @/P.
pose M w sg := BRM.big predT (fun x => F x (sg x)) w.
pose G w1 w2 sg :=
  if u = sg x /\ fixfinfun (mem w1) (mem s) sg then M w2 sg else 0%r.
rewrite -(@eq_sum (G (x :: r) (x :: r))) => /= [sg @/G|].
- by case: (u = sg x).
rewrite -(@eq_sum (fun sg => F x u * G (x :: r) r sg)).
- by move=> sg /= @/G; case _: (_ /\ _).
rewrite sumZ; congr => @/G @/M => {S P M G}.
rewrite -(@sum_reindex (swap_codom x witness u)) /(\o) /=.
- by apply: bij_swap_codom.
- by apply/summable_cond_fin/finiteIr/finite_fixfinfun; apply/finite_mem.
apply: eq_sum=> /= sg; congr; last first.
- rewrite !BRM.big_seq &(BRM.eq_bigr) => /= y y_in_r.
  by case: (x = y) => [->>//|ne_xy]; rewrite swap_codom_neq.
apply: eq_iff; split.
- case=> sgx ond y; have /= := ond y; case: (y = x) => [->>|] /=.
  - move=> _; rewrite x_notin_r /=; move: sgx.
    rewrite /swap_codom /=; case _: (sg x = _) => //= ?.
    by rewrite [sg x = u]eq_sym; case: (u = sg x).
  - by move=> ne_yx; rewrite swap_codom_neq //= eq_sym.
- move=> ^ond /(_ x); rewrite x_notin_r /= => sgx; split.
  - by rewrite /swap_codom /= sgx.
  - move=> y /=; case: (y = x) => [->>|] /=.
    - by rewrite /swap_codom /= sgx.
    - by move=> ne_yx; rewrite swap_codom_neq -1:&(ond) eq_sym.
qed.

(* -------------------------------------------------------------------- *)
lemma prodrDl2 (f g : 't -> real) r : is_finite_for predT r =>
    BRM.big predT (fun x => f x + g x) r
  = sum (fun sigma => BRM.big predT (fun x => if sigma x then f x else g x) r).
proof.
case=> [uq_r mem_r]; pose F x b := if b then f x else g x.
have eq := prodrDl F r [true; false] _ _ => //.
apply: (eq_trans _ eq); apply: eq_sum => /= sg.
have ->: mem r = predT by apply/fun_ext=> ?; rewrite mem_r.
by have ->: mem [true; false] = predT by apply/fun_ext; case.
qed.
