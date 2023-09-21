(* -------------------------------------------------------------------- *)
require import AllCore Bool Ring StdRing StdOrder StdBigop List RealExp.
(*---*) import IterOp Bigreal.BRA IntID RField IntOrder RealOrder.

pragma +implicits.

(* -------------------------------------------------------------------- *)
op convergeto (s : int -> real) (x : real) =
  forall epsilon, 0%r < epsilon => exists N,
    forall n, (N <= n)%Int => `|s n - x| < epsilon.

op converge (s : int -> real) =
  exists l, convergeto s l.

op bounded_by (s : int -> real) (M : real) =
  exists N, forall n, (N <= n)%Int => `|s n| <= M.

op bounded (s : int -> real) =
  exists M, bounded_by s M.

op monotone (s : int -> real) =
  forall n, 0 <= n => s n <= s (n+1).

(* -------------------------------------------------------------------- *)
lemma boundedP (s : int -> real):
  (exists M, 0%r <= M /\ bounded_by s M) <=> bounded s.
proof.
split; case=> [M [_ leM]|M ^leM [N lesM]]; first by exists M.
by exists M; rewrite leM /= (ler_trans `|s N|) 1:normr_ge0 // lesM.
qed.

lemma boundedC c : bounded (fun x => c).
proof. by exists `|c| 0. qed.

(* -------------------------------------------------------------------- *)
lemma cnvP l s: convergeto s l => converge s.
proof. by move=> cnv_sl; exists l. qed.

(* -------------------------------------------------------------------- *)
lemma bounded_cnvto l (s : int -> real) :
  convergeto s l => bounded s.
proof.
move=> /(_ 1%r) /= [N] les1; exists (1%r + `|l|) N.
move=> n /les1 /ltrW lesn1; rewrite -(addrK l (s n)) addrAC.
apply/(ler_trans (`|s n - l| + `|l|)); 1: by apply/ler_norm_add.
by rewrite ler_add2r.
qed.

(* -------------------------------------------------------------------- *)
lemma monotoneP (s : int -> real):
  monotone s <=> (forall m n, 0 <= m <= n => s m <= s n).
proof.
split=> [h m n|h n]; last first.
  by move=> ge0n; apply/h; rewrite ge0n ler_addl.
case=> ge0m; rewrite -IntOrder.subr_ge0 -{2}(@IntID.subrK n m).
elim: (n - m)=> // i ge0i ih; rewrite addrAC (ler_trans _ ih) //.
by rewrite h ?addr_ge0.
qed.

lemma uniq_cnvto s x y: convergeto s x => convergeto s y => x = y.
proof.
move=> lim_sx lim_sy; case: (x = y)=> // ne_xy.
pose e := `|x - y| / 2%r; have gt0e: 0%r < e.
  by rewrite /e divr_gt0 ?(normr_gt0, subr_eq0).
case: (lim_sx _ gt0e) => {lim_sx} Nx lim_sx.
case: (lim_sy _ gt0e) => {lim_sy} Ny lim_sy.
case: (IntOrder.maxr_ub Nx Ny); (pose N := max _ _).
move=> /lim_sx {lim_sx} lim_sx /lim_sy {lim_sy} lim_sy.
have := ltr_add _ _ _ _ lim_sx lim_sy; rewrite ltrNge.
by rewrite /e double_half (@distrC (s N)) ler_dist_add.
qed.

(* -------------------------------------------------------------------- *)
lemma eq_cnvto_from N s1 s2 l:
     (forall n, (N <= n)%Int => s1 n = s2 n)
  => convergeto s1 l => convergeto s2 l.
proof.
move=> eq_s lim_s1 e gt0_e; case: (lim_s1 _ gt0_e).
move=> Ns lim_s1N; exists (max N Ns)=> n /IntOrder.ler_maxrP [leN leNs].
by rewrite -eq_s // lim_s1N.
qed.

lemma eq_cnvto s1 s2 l:
  (forall n, s1 n = s2 n) => convergeto s1 l => convergeto s2 l.
proof. by move=> eq; apply/(@eq_cnvto_from 0)=> n _; apply/eq. qed.

lemma eq_cnvto_fromP N s1 s2 l:
     (forall n, (N <= n)%Int => s1 n = s2 n)
  => convergeto s1 l <=> convergeto s2 l.
proof.
move=> eq; split; apply/(eq_cnvto_from N)=> // n leNn.
by rewrite eq_sym eq.
qed.

(* -------------------------------------------------------------------- *)
lemma eq_cnv_fromP N s1 s2:
     (forall n, (N <= n)%Int => s1 n = s2 n)
  => converge s1 <=> converge s2.
proof.
move=> eq; split; case=> l h; exists l; move: h.
  by apply/(@eq_cnvto_from N).
by apply/(@eq_cnvto_from N)=> n leNn; apply/eq_sym/eq.
qed.

(* -------------------------------------------------------------------- *)
lemma nz_cnvto l (s : int -> real) :
  l <> 0%r => convergeto s l => exists N, forall n, (N <= n)%Int => s n <> 0%r.
proof.
move=> nz_l /(_ (`|l| / 2%r) _).
- by rewrite mulr_gt0 ?invr_gt0 // normr_gt0.
case=> N cnv; exists N => n ge_N_n; rewrite -normr_gt0.
apply: (@ltr_trans (`|l| / 2%r)); first by rewrite divr_gt0 // normr_gt0.
have ->: `|l| / 2%r = `|l| - `|l| / 2%r by field.
apply: (@ltr_le_trans (`|l| - `|s n - l|)).
- by rewrite ltr_add2l ltr_opp2 &(cnv).
have /ler_trans := ler_sub_norm_add l (s n - l); apply.
by apply: lerr_eq; congr; ring.
qed.

(* -------------------------------------------------------------------- *)
lemma cnvtoC c: convergeto (fun x => c) c.
proof. by move=> e gt0e; exists 0 => n _; rewrite subrr. qed.

lemma cnvtoD s1 s2 l1 l2: convergeto s1 l1 => convergeto s2 l2 =>
  convergeto (fun x => s1 x + s2 x) (l1 + l2).
proof.
move=> cnv1 cnv2 e gt0e; have gt0e2: 0%r < e/2%r by rewrite divr_gt0.
case: (cnv1 _ gt0e2)=> N1 c1; case: (cnv2 _ gt0e2)=> N2 c2.
exists (max N1 N2) => n /IntOrder.ler_maxrP [le_N1n le_N2n].
(* FIXME ICI `|s1 n + s2 n - (l1 + l2)| < e --> `|s1 n + s2 n - (l1 + l2)| < e *)
pose x := `|s1 n - l1| + `|s2 n - l2|.
apply (@ler_lt_trans x); rewrite /x => {x}.
  by rewrite subrACA; apply/ler_norm_add.
by rewrite -(@double_half e) ltr_add ?(c1, c2).
qed.

lemma cnvtoDr0 s2 s1 l: convergeto s2 0%r => convergeto s1 l =>
  convergeto (fun x => s1 x + s2 x) l.
proof. by move=> cv1 cv2; rewrite -(@addr0 l); apply/cnvtoD. qed.

lemma cnvtoD0r s1 s2 l: convergeto s1 0%r => convergeto s2 l =>
  convergeto (fun x => s1 x + s2 x) l.
proof. by move=> cv1 cv2; rewrite -(@add0r l); apply/cnvtoD. qed.

lemma cnvtoN s l: convergeto s l => convergeto (fun x => -(s x)) (-l).
proof.
move=> cnv e /cnv [N {cnv} cnv]; exists N => n /cnv h.
by rewrite -opprD normrN.
qed.

lemma cnvtoB s1 s2 l1 l2:
  convergeto s1 l1 => convergeto s2 l2 =>
  convergeto (fun x => s1 x - s2 x) (l1 - l2).
proof.
by move=> cv1 /cnvtoN cvN2; have := cnvtoD _ _ _ _ cv1 cvN2; apply/eq_cnvto.
qed.

lemma cnvtoBlim s l: convergeto s l =>
  convergeto (fun x => s x - l) 0%r.
proof. by move=> cv; rewrite -(@subrr l); apply/cnvtoB/cnvtoC. qed.

lemma cnvtoZ c s l: convergeto s l => convergeto (fun x => c * s x) (c * l).
proof.
move=> cnv e gt0e; case: (c = 0%r) => [->|nz_c].
  by exists 0 => n _ /=; rewrite normr0.
have: 0%r < e / `|c| by rewrite divr_gt0 // normr_gt0.
move/cnv=> [N {cnv} cnv]; exists N => n /cnv.
rewrite -mulrBr normrM -(@ltr_pmul2l `|c|) ?normr_gt0 //.
by rewrite mulrCA mulrV 1:normr0P.
qed.

lemma cnvtoM_boundedr s1 s2: convergeto s1 0%r => bounded s2 =>
  convergeto (fun x => s1 x * s2 x) 0%r.
proof.
move=> c1 /boundedP [M] [ge0_M] [N leM] e gt0_e.
have /= [N' lee] := c1 (e / (M + 1%r)) _.
  by rewrite divr_gt0 ?ltr_spaddr // (ler_trans `|s2 N|).
exists (max N N')=> n /= /IntOrder.ler_maxrP [leNn leN'n]; rewrite normrM.
apply/(ler_lt_trans (M * (e / (M + 1%r)))); last first.
  rewrite mulrCA gtr_pmulr // ltr_pdivr_mulr.
  by rewrite ltr_spaddr. by rewrite mul1r ltr_addl.
by rewrite mulrC ler_pmul ?normr_ge0 // ?leM //; apply/ltrW/lee.
qed.

lemma cnvtoM_boundedl s1 s2: convergeto s2 0%r => bounded s1 =>
  convergeto (fun x => s1 x * s2 x) 0%r.
proof.
move=> c2 b1; have := cnvtoM_boundedr _ _ c2 b1.
by apply/eq_cnvto=> n /=; rewrite mulrC.
qed.

lemma cnvtoM s1 s2 l1 l2:
  convergeto s1 l1 => convergeto s2 l2 =>
  convergeto (fun x => s1 x * s2 x) (l1 * l2).
proof.
pose a1 := fun n => s1 n - l1; pose a2 := fun n => s2 n - l2.
pose F := fun x => l1 * l2 + l1 * a2 x + a1 x * s2 x.
move=> cv1 cv2; apply/(@eq_cnvto F _) => @/F.
  by move=> n @/a1 @/a2 /=; ring.
apply/cnvtoDr0/cnvtoDr0/cnvtoC; last first.
  by move=> @/a2; apply/cnvtoM_boundedl/boundedC/cnvtoBlim.
move=> @/a1; apply/cnvtoM_boundedr; first by apply/cnvtoBlim.
by apply/(@bounded_cnvto l2).
qed.

lemma cnvto_pow p : -1%r < p < 1%r => convergeto (fun (n : int) => p ^ n) 0%r.
proof.
move=> [h0p hp1] eps he /=.
case: (p = 0%r) => [-> | ?].
+ by exists 1 => n hn; rewrite RField.expr0n /#.
pose P := `|p|.
have [# 4?] : 0%r < P < 1%r /\ P <> 0%r /\ 0%r <= P by smt().  
case: (1%r <= eps) => h1e.
+  exists 1 => n hn; apply (ler_lt_trans (`|p|^1)).
   + rewrite normrX; smt(ler_wiexpn2l expr_ge0).
   smt(RField.expr1).
pose N := ceil (-log (inv P) eps) + 1; exists N => n hn.
rewrite normrX -/P.
have ? : 1%r < inv P by apply invr_gt1.
have ? : 0 < N by smt (log_le0 ceil_bound).
apply (ler_lt_trans (P ^ N)); 1: by apply ler_wiexpn2l => /#. 
rewrite -(RField.invrK P) -RField.exprN1 -RField.exprM /= mulN1r.
rewrite -(@log_mono_ltr (inv P)) //; 1: by apply/expr_gt0/invr_gt0.
rewrite -rpow_int 1:invr_ge0 // logK 1:invr_gt0 1:// 1:/#.
smt(ceil_bound). 
qed.

(* -------------------------------------------------------------------- *)
lemma cnvtoV_nz l (s : int -> real) :
     l <> 0%r
  => convergeto s l
  => convergeto (fun (n : int) => inv (s n)) (inv l).
proof.
move=> nz_l cnv e gt0_e; case: (nz_cnvto l s nz_l cnv) => N1 nz_s.
have eq_un: forall n, (N1 <= n)%Int =>
  `|inv (s n) - inv l| = `|s n - l| / (`|s n| * `|l|).
- move=> n /nz_s => nz_sn; rewrite -(@div1r (s n)) -(@div1r l).
  rewrite -mulNr fracrDE //= mulN1r distrC.
  by rewrite !(normrM, normrV) //= mulf_neq0.
case: (cnv (`|l| / 2%r) _) => [|N2 bd_snBl].
- by rewrite divr_gt0 // normr_gt0.
have bd_halfl: forall n, N2 <= n => `|l| / 2%r < `|s n|.
- move=> n /bd_snBl bd; apply (@ltr_le_trans (`|l| - `|s n - l|)).
  - have ->: `|l| / 2%r = `|l| - `|l| / 2%r by field.
    by apply/ltr_add2l/ltr_opp2.
  by rewrite distrC {2}(_ : s n = l - (l - s n)) 1:#ring &(ler_sub_dist).
have bd_un: forall n, N1 <= n => N2 <= n =>
  `|inv (s n) - inv l| <= (2%r / `|l| ^ 2) * `|s n - l|.
- move=> n ^/eq_un -> /nz_s nz_sn le_N2_n.
  rewrite mulrC &(ler_wpmul2r); first by apply: normr_ge0.  
  rewrite expr2 !invrM ?normr0P // mulrCA.
  apply: ler_wpmul2l; first by rewrite invr_ge0 normr_ge0.
  rewrite -invf_div lef_pinv 1?divr_gt0 ?normr_gt0 //.
  by apply/ltrW/bd_halfl.
have := cnv (`|l| ^ 2 / 2%r * e) _.
- by rewrite mulr_gt0 // divr_gt0 // expr_gt0 normr_gt0.
case=> N3 bde; exists (max (max N1 N2) N3) => n.
case/IntOrder.ler_maxrP=> /IntOrder.ler_maxrP [] 3?.
have /ler_lt_trans := bd_un n _ _ => //; apply.
rewrite -invf_div; have := bde n _ => //; pose d := _ / _.
have gt0_d: 0%r < d by rewrite divr_gt0 // expr_gt0 normr_gt0.
rewrite -(@ltr_pmul2l (inv d)) 1:&(invr_gt0) //.
by move/ltr_le_trans; apply; apply/lerr_eq; field; apply/gtr_eqF.
qed.

(* -------------------------------------------------------------------- *)
lemma le_cnvto_from s1 s2 l1 l2:
     (exists N, forall n, (N <= n)%Int => (s1 n <= s2 n)%Real)
  => convergeto s1 l1 => convergeto s2 l2 => l1 <= l2.
proof.
case=> N le_s12 cv1 cv2; pose F := fun x => s1 x - s2 x.
have cvF: convergeto F (l1 - l2) by move=> @/F; apply/cnvtoB.
apply/lerNgt/negP=> lt_l21; pose e := (l1 - l2) / 2%r.
have gt0_e: 0%r < e by rewrite /e divr_gt0 ?subr_gt0.
have [N' lte] := cvF _ gt0_e; pose n := max N N'.
have /subr_le0 le0_s12 := le_s12 n _; first by rewrite /n maxrl.
have := lte n _; first by rewrite /n maxrr.
rewrite ltr_norml => -[+ _]; rewrite ltr_subr_addl /F.
move/ltr_le_trans/(_ _ le0_s12); rewrite -(@mulr1 (l1-l2)) /e.
rewrite -mulrBr pmulr_llt0 1:subr_gt0 1:invr_lt1 //.
by rewrite subr_lt0 ltrNge (ltrW lt_l21).
qed.

(* -------------------------------------------------------------------- *)
lemma cnvto_lub_bmono_from (s : int -> real) M N :
     (forall n p, (N <= n <= p)%Int => s n <= s p)
  => (forall n, N <= n => s n <= M)
  => convergeto s (lub (fun x => exists n, N <= n /\ s n = x)).
proof.
move=> mono_s bd_s; pose E x := exists n, N <= n /\ s n = x.
have: has_lub E; first (split; first by exists (s N) N).
+ by exists M => x [n [leNn <-]]; apply/bd_s.
move=> ^/lub_upper_bound h1 /lub_adherent h2.
move=> e gt0_e; case/(_ _ gt0_e): h2 => _ [[K] [leKn <<-]] h2.
exists K => n leNn; rewrite distrC ger0_norm ?subr_ge0.
+ by apply/h1; exists n => /=; apply/(@lez_trans K).
by rewrite ltr_subl_addr -ltr_subl_addl; apply/(ltr_le_trans _ h2)/mono_s.
qed.

(* -------------------------------------------------------------------- *)
lemma cnv_bmono_from (s : int -> real) M N :
     (forall n p, (N <= n <= p)%Int => s n <= s p)
  => (forall n, N <= n => s n <= M)
  => converge s.
proof.
move=> h1 h2; exists (lub (fun x => exists n, N <= n /\ s n = x)).
by apply/(@cnvto_lub_bmono_from _ M N).
qed.

(* -------------------------------------------------------------------- *)
lemma cnvC (x:real) : converge (fun _ => x).
proof. by exists x => eps he; exists 0. qed.

lemma cnvD (s1 s2 : int -> real) :
  converge s1 => converge s2 => converge (fun x => s1 x + s2 x).
proof. by case=> [l1 h1] [l2 h2]; exists (l1 + l2); apply/cnvtoD. qed.

lemma cnvZ c (s : int -> real) :
  converge s => converge (fun x => c * s x).
proof. by case=> [l h]; exists (c * l); apply/cnvtoZ. qed.

lemma cnvZ_iff c (s : int -> real) : c <> 0%r =>
  converge (fun x => c * s x) <=> converge s.
proof.
move=> nz_c; split; last by apply/cnvZ.
suff {2}->: s = fun x => inv c * (c * s x) by apply/cnvZ.
by apply/fun_ext=> x; rewrite mulrA (@mulrC _ c) divff.
qed.

lemma cnvN s : converge s => converge (fun x => -s x).
proof. by move/(@cnvZ (-1)%r) => /#. qed.

lemma cnvB s1 s2 :
  converge s1 => converge s2 => converge (fun x => s1 x - s2 x).
proof.  by move=> h1 h2; rewrite cnvD // cnvN. qed.

lemma cnv_pow p : -1%r < p < 1%r => converge (fun (n : int) => p ^ n).
proof. by move=> ?; exists 0%r; apply cnvto_pow. qed.

(* -------------------------------------------------------------------- *)
op lim (s : int -> real) =
  choiceb (fun l => convergeto s l) 0%r.

(* -------------------------------------------------------------------- *)
lemma limP (s : int -> real):
  converge s <=> convergeto s (lim s).
proof. by split=> [/choicebP /(_ 0%r)|lims]; last exists (lim s). qed.

lemma lim_cnvto (s : int -> real) l:
  convergeto s l => lim s = l.
proof. by move=> ^h /cnvP /limP /uniq_cnvto; apply. qed.

lemma lim_Ncnv (s : int -> real):
  !converge s => lim s = 0%r.
proof. by move=> h; apply/choiceb_dfl/negb_exists. qed.

lemma lim_eq (N : int) (s1 s2 : int -> real):
     (forall n, N <= n => s1 n = s2 n)
  => lim s1 = lim s2.
proof. move=> eq.
case: (converge s1) => ^cv1; rewrite (@eq_cnv_fromP N _ s2) // => cv2;
  last by rewrite !lim_Ncnv.
apply/lim_cnvto; case: cv2 => [l2 ^c2 /lim_cnvto ->]; move: c2.
by apply/(@eq_cnvto_from N)=> n leNn; apply/eq_sym/eq.
qed.

(* -------------------------------------------------------------------- *)
lemma geC_lim_from (N : int) (s : int -> real) (c : real) :
     (forall n, N <= n => c <= s n)
  => converge s
  => c <= lim s.
proof.
move=> le cvg; apply: (@le_cnvto_from (fun _ => c) s c (lim s)).
- by exists N.
- by apply: cnvtoC.
- by apply/limP.
qed.

(* -------------------------------------------------------------------- *)
lemma leC_lim_from (N : int) (s : int -> real) (c : real) :
     (forall n, N <= n => s n <= c)
  => converge s
  => lim s <= c.
proof.
move=> le cvg; apply: (@le_cnvto_from s (fun _ => c) (lim s) c).
- by exists N.
- by apply/limP.
- by apply: cnvtoC.
qed.

(* -------------------------------------------------------------------- *)
lemma limC_eq_from (N : int) c (s : int -> real) :
   (forall n, N <= n => s n = c) => lim s = c.
proof. by move/lim_eq=> ->; have /lim_cnvto := cnvtoC c. qed.

lemma limC_eq c (s : int -> real) :
 (forall n, 0 <= n => s n = c) => lim s = c.
proof. by apply/limC_eq_from. qed.

lemma limC c : lim (fun x => c) = c.
proof. by apply/limC_eq. qed.

lemma limZ c (s : int -> real) :
  lim (fun x => c * s x) = c * lim s.
proof.
case: (converge s) => [[l] ^/cnvtoZ /(_ c) h1 h2|].
+ by rewrite (lim_cnvto h1) (lim_cnvto h2).
case: (c = 0%r) => [-> _ /=|nz_c ^h1]; first by rewrite limC.
by rewrite -(@cnvZ_iff c) // => h2; rewrite !lim_Ncnv.
qed.

lemma limD (s1 s2 : int -> real) :
  converge s1 => converge s2 =>
    lim (fun x => s1 x + s2 x) = lim s1 + lim s2.
proof.
case=> [l1 h1] [l2 h2]; rewrite (lim_cnvto h1) (lim_cnvto h2).
by have := cnvtoD _ _ _ _ h1 h2 => /lim_cnvto ->.
qed.

lemma limN (s : int -> real) : lim (fun x => - s x) = - lim s.
proof. by rewrite -mulN1r -limZ; congr=> /#. qed.

lemma limB (s1 s2 : int -> real) :
  converge s1 => converge s2 =>
    lim (fun x => s1 x - s2 x) = lim s1 - lim s2.
proof. by move=> h1 h2; rewrite limD // 1:cnvN // limN. qed.

lemma limM (s1 s2 : int -> real) :
  converge s1 => converge s2 =>
    lim (fun x => s1 x * s2 x) = lim s1 * lim s2.
proof.
case=> [l1 h1] [l2 h2]; rewrite (lim_cnvto h1) (lim_cnvto h2).
by have := cnvtoM _ _ _ _ h1 h2 => /lim_cnvto ->.
qed.

lemma lim_pow p : -1%r < p < 1%r => lim (fun (n:int) => p ^ n) = 0%r.
proof. by move=> h; apply/lim_cnvto/cnvto_pow. qed.

(* -------------------------------------------------------------------- *)
lemma convergeto_sum
  (P : 'a -> bool)
  (F : 'a -> int -> real)
  (l : 'a -> real)
  (s : 'a list)
:
     (forall x, P x => convergeto (F x) (l x))
  => convergeto
       (fun n => big P (fun x => (F x n)) s)
       (big P (fun x => l x) s).
proof.
move=> cvg; elim: s => /= [|x s ih].
- by rewrite !big_nil &(@eq_cnvto (fun _ => 0%r)) //= &(cnvtoC).
rewrite big_cons; case: (P x) => [Px|NPx]; last first.
- rewrite &(@eq_cnvto (fun n => big P (fun y => F y n) s)) /=.
  - by move=> n; rewrite big_cons NPx.
  - apply: ih.
pose G (n : int) := F x n + big P (fun y => F y n) s.
rewrite &(eq_cnvto G) => /= [n|].
- by rewrite /G big_cons Px.
by apply: cnvtoD => //; apply: cvg.
qed.

lemma converge_sum
  (P : 'a -> bool)
  (F : 'a -> int -> real)
  (s : 'a list)
:
     (forall x, P x => converge (F x))
  => converge (fun n => big P (fun x => (F x n)) s).
proof.
move=> cvg; pose l := big P (fun x => lim (F x)) s.
apply/(cnvP l)/convergeto_sum => /= x Px.
by apply/limP/cvg.
qed.

lemma lim_sum 
  (P : 'a -> bool)
  (F : 'a -> int -> real)
  (s : 'a list)
:
     (forall x, P x => converge (F x))
  => big P (fun x => lim (F x)) s
     = lim (fun n => big P (fun x => F x n) s).
proof.
move=> cvg; pose l := fun x => lim (F x).
have {cvg}cvg: forall x, P x => convergeto (F x) (l x).
- by move=> x Px; apply/limP/cvg.
by move/convergeto_sum: cvg => /(_ s) /lim_cnvto => <-.
qed.
