(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2016 - Inria
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
require import Bool Option Fun Distr Int IntExtra Real RealExtra.
require import Ring StdRing StdOrder StdBigop List.
(*---*) import IterOp Bigreal.BRA IntID RField IntOrder RealOrder.
require import NewLogic.

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
case: (max_is_ub Nx Ny); (pose N := max _ _).
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
move=> Ns lim_s1N; exists (max N Ns)=> n /geq_max [leN leNs].
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
lemma cnvtoC c: convergeto (fun x => c) c.
proof. by move=> e gt0e; exists 0 => n _; rewrite subrr. qed.

lemma cnvtoD s1 s2 l1 l2: convergeto s1 l1 => convergeto s2 l2 =>
  convergeto (fun x => s1 x + s2 x) (l1 + l2).
proof.
move=> cnv1 cnv2 e gt0e; have gt0e2: 0%r < e/2%r by rewrite divr_gt0.
case: (cnv1 _ gt0e2)=> N1 c1; case: (cnv2 _ gt0e2)=> N2 c2.
exists (max N1 N2) => n /geq_max [le_N1n le_N2n].
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
exists (max N N')=> n /= /geq_max [leNn leN'n]; rewrite normrM.
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

(* -------------------------------------------------------------------- *)
lemma le_cnvto_form s1 s2 l1 l2:
     (exists N, forall n, (N <= n)%Int => (s1 n <= s2 n)%Real)
  => convergeto s1 l1 => convergeto s2 l2 => l1 <= l2.
proof.
case=> N le_s12 cv1 cv2; pose F := fun x => s1 x - s2 x.
have cvF: convergeto F (l1 - l2) by move=> @/F; apply/cnvtoB.
apply/lerNgt/negP=> lt_l21; pose e := (l1 - l2) / 2%r.
have gt0_e: 0%r < e by rewrite /e divr_gt0 ?subr_gt0.
have [N' lte] := cvF _ gt0_e; pose n := max N N'.
have /subr_le0 le0_s12:= le_s12 n _; first by rewrite /n leq_maxl.
have := lte n _; first by rewrite /n leq_maxr.
rewrite ltr_norml => -[+ _] @/F; rewrite ltr_subr_addl /F.
move/ltr_le_trans/(_ _ le0_s12); rewrite -(@mulr1 (l1-l2)) /e.
rewrite -mulrBr pmulr_llt0 1:subr_gt0 1:invr_lt1 //.
by rewrite subr_lt0 ltrNge (ltrW lt_l21).
qed.

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
lemma limC_eq_from (N : int) c (s : int -> real) :
   (forall n, N <= n => s n = c) => lim s = c.
proof. by move/lim_eq=> ->; have /lim_cnvto := cnvtoC c. qed.

lemma limC_eq c (s : int -> real) :
 (forall n, 0 <= n => s n = c) => lim s = c.
proof. by apply/limC_eq_from. qed.

lemma limC c : lim (fun x => c) = c.
proof. by apply/limC_eq. qed.
