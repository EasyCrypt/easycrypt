(* -------------------------------------------------------------------- *)
require import AllCore Bool Ring StdRing StdOrder StdBigop List.
(*---*) import IterOp Bigreal.BRA IntID RField IntOrder RealOrder.

pragma +implicits.

(* -------------------------------------------------------------------- *)
op convergeto (s : int -> real) (x : real) =
  forall epsilon, 0%r < epsilon => exists N,
    forall n, (N <= n)%Int => `|s n - x| < epsilon.

op convergetopi (s : int -> real) =
  forall M, exists N, forall n,
    (N <= n)%Int => M < s n.

op convergetoni (s : int -> real) =
  forall M, exists N, forall n,
    (N <= n)%Int => s n < M.

op converge (s : int -> real) =
  exists l, convergeto s l.

op bounded_by (s : int -> real) (M : real) =
  exists N, forall n, (N <= n)%Int => `|s n| <= M.

op bounded (s : int -> real) =
  exists M, bounded_by s M.

(*TODO: should be called increasing, not monotone.*)
op monotone (s : int -> real) =
  forall n, 0 <= n => s n <= s (n+1).

op bigO (s : int -> real) (t : int -> real) =
  bounded (fun n => t n / s n).

op smallo (s : int -> real) (t : int -> real) =
  convergeto (fun n => t n / s n) 0%r.

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

lemma bounded_cnv (s : int -> real) :
  converge s => bounded s.
proof. by case=> l; apply/bounded_cnvto. qed.

lemma bounded_cnvtopi (s : int -> real) :
  convergetopi s => !bounded s.
proof.
move=> lim_s; apply/negP=> -[M] [N1] bnd_s.
case/(_ M): lim_s => N2; move: bnd_s.
move=> /(_ (max N1 N2)) /(_ _); [by apply/IntOrder.maxrl|move=> bnd_s].
move=> /(_ (max N1 N2)) /(_ _); [by apply/IntOrder.maxrr|move=> lim_s].
move: (ler_lt_trans _ _ _ bnd_s lim_s) => /=.
by rewrite -lerNgt; apply/ler_norm.
qed.

lemma bounded_cnvtoni (s : int -> real) :
  convergetopi s => !bounded s.
proof.
move=> lim_s; apply/negP=> -[M] [N1] bnd_s.
case/(_ M): lim_s => N2; move: bnd_s.
move=> /(_ (max N1 N2)) /(_ _); [by apply/IntOrder.maxrl|move=> bnd_s].
move=> /(_ (max N1 N2)) /(_ _); [by apply/IntOrder.maxrr|move=> lim_s].
move: (ler_lt_trans _ _ _ bnd_s lim_s) => /=.
by rewrite -lerNgt; apply/ler_norm.
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

lemma monotone_cnv (s : int -> real):
  monotone s => converge s \/ convergetopi s.
proof.
move/monotoneP=> mono_s; case: (convergetopi s) => //=.
rewrite negb_forall /= => -[M]; rewrite negb_exists /=.
move=> ltM_; pose S:= (fun x => exists n, 0 <= n /\ x = s n).
exists (lub S) => e lt0e; have lubS: has_lub S.
+ split; [by exists (s 0); exists 0|].
  exists M => x [n] [le0n ->>]; move/(_ n): ltM_.
  rewrite negb_forall => -[m] /=; rewrite negb_imply.
  by rewrite -lerNgt => -[lenm]; apply/ler_trans/mono_s; split.
case: (lub_adherent _ lubS _ lt0e) => ? [[N] [le0N ->>]].
move/ltr_subl_addl/ltr_subl_addr=> lt_e; exists N.
move=> n leNn; apply/ltr_norml; rewrite -ltr_subl_addr /=; split.
+ move: (mono_s N n); rewrite le0N leNn /=; apply/ltr_le_trans.
  by rewrite addrC; apply/ltr_subl_addl/ltr_subl_addr.
move=> _; move: lt0e; apply/ler_lt_trans/subr_le0.
move: (lub_upper_bound _ lubS (s n) _) => //.
by exists n; split => //; apply/(IntOrder.ler_trans N).
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
lemma eq_bounded_by_from N s1 s2 M:
     (forall n, (N <= n)%Int => s1 n = s2 n)
  => bounded_by s1 M => bounded_by s2 M.
proof.
move=> eq_s [N'] bb_s1N'; exists (max N N') => n /IntOrder.ler_maxrP [leNn leN'n].
by rewrite -eq_s // bb_s1N'.
qed.

lemma eq_bounded_by s1 s2 M:
  (forall n, s1 n = s2 n) => bounded_by s1 M => bounded_by s2 M.
proof. by move=> eq; apply/(@eq_bounded_by_from 0)=> n _; apply/eq. qed.

lemma eq_bounded_by_fromP N s1 s2 M:
     (forall n, (N <= n)%Int => s1 n = s2 n)
  => bounded_by s1 M <=> bounded_by s2 M.
proof.
move=> eq; split; apply/(eq_bounded_by_from N)=> // n leNn.
by rewrite eq_sym eq.
qed.

(* -------------------------------------------------------------------- *)
lemma eq_bounded_from N s1 s2:
     (forall n, (N <= n)%Int => s1 n = s2 n)
  => bounded s1 => bounded s2.
proof. by move=> eq_s [M] bb_s; exists M; move: eq_s bb_s; apply/eq_bounded_by_from. qed.

lemma eq_bounded s1 s2:
  (forall n, s1 n = s2 n) => bounded s1 => bounded s2.
proof. by move=> eq; apply/(@eq_bounded_from 0)=> n _; apply/eq. qed.

lemma eq_bounded_fromP N s1 s2:
     (forall n, (N <= n)%Int => s1 n = s2 n)
  => bounded s1 <=> bounded s2.
proof.
move=> eq; split; apply/(eq_bounded_from N)=> // n leNn.
by rewrite eq_sym eq.
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
lemma eq_cnvtopi_from N s1 s2:
     (forall n, (N <= n)%Int => s1 n = s2 n)
  => convergetopi s1 => convergetopi s2.
proof.
move=> eq_s lim_s1 M; case: (lim_s1 M)=> Ns lim_s1N.
exists (max N Ns)=> n /IntOrder.ler_maxrP [leN leNs].
by rewrite -eq_s // lim_s1N.
qed.

lemma eq_cnvtopi s1 s2:
  (forall n, s1 n = s2 n) => convergetopi s1 => convergetopi s2.
proof. by move=> eq; apply/(@eq_cnvtopi_from 0)=> n _; apply/eq. qed.

lemma eq_cnvtopi_fromP N s1 s2:
     (forall n, (N <= n)%Int => s1 n = s2 n)
  => convergetopi s1 <=> convergetopi s2.
proof.
move=> eq; split; apply/(eq_cnvtopi_from N)=> // n leNn.
by rewrite eq_sym eq.
qed.

(* -------------------------------------------------------------------- *)
lemma eq_cnvtoni_from N s1 s2:
     (forall n, (N <= n)%Int => s1 n = s2 n)
  => convergetoni s1 => convergetoni s2.
proof.
move=> eq_s lim_s1 M; case: (lim_s1 M)=> Ns lim_s1N.
exists (max N Ns)=> n /IntOrder.ler_maxrP [leN leNs].
by rewrite -eq_s // lim_s1N.
qed.

lemma eq_cnvtoni s1 s2:
  (forall n, s1 n = s2 n) => convergetoni s1 => convergetoni s2.
proof. by move=> eq; apply/(@eq_cnvtoni_from 0)=> n _; apply/eq. qed.

lemma eq_cnvtoni_fromP N s1 s2:
     (forall n, (N <= n)%Int => s1 n = s2 n)
  => convergetoni s1 <=> convergetoni s2.
proof.
move=> eq; split; apply/(eq_cnvtoni_from N)=> // n leNn.
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
lemma bounded_byC (c : real): bounded_by (fun x => c) `|c|.
proof. by trivial. qed.

lemma bounded_byD s1 s2 M1 M2: bounded_by s1 M1 => bounded_by s2 M2 =>
  bounded_by (fun x => s1 x + s2 x) (M1 + M2).
proof.
move=> [N1] le_1 [N2] le_2; exists (max N1 N2) => n.
move=> /IntOrder.ler_maxrP [leN1n leN2n].
move: le_1 le_2 => /(_ _ leN1n) le_1 /(_ _ leN2n) le_2.
by move: (ler_add _ _ _ _ le_1 le_2); apply/ler_trans/ler_norm_add.
qed.

lemma bounded_byN s M: bounded_by s M => bounded_by (fun x => -(s x)) M.
proof. by move=> [N] le_; exists N => n; rewrite normrN; apply/le_. qed.

lemma bounded_byB s1 s2 M1 M2:
  bounded_by s1 M1 => bounded_by s2 M2 =>
  bounded_by (fun x => s1 x - s2 x) (M1 + M2).
proof. by move=> bb1 /bounded_byN bb2; apply/bounded_byD. qed.

lemma bounded_byZ c s M: bounded_by s M => bounded_by (fun x => c * s x) (`|c| * M).
proof.
move=> [N] le_; exists N => n leNn; move/(_ _ leNn): le_.
by rewrite normrM; apply/ler_wpmul2l/normr_ge0.
qed.

lemma bounded_byM s1 s2 M1 M2: bounded_by s1 M1 => bounded_by s2 M2 =>
  bounded_by (fun x => s1 x * s2 x) (M1 * M2).
proof.
move=> [N1] le_1 [N2] le_2; exists (max N1 N2) => n.
move=> /IntOrder.ler_maxrP [leN1n leN2n].
move: le_1 le_2 => /(_ _ leN1n) le_1 /(_ _ leN2n) le_2.
by rewrite normrM; apply/ler_pmul => //; apply/normr_ge0.
qed.

(* -------------------------------------------------------------------- *)
lemma boundedD s1 s2: bounded s1 => bounded s2 =>
  bounded (fun x => s1 x + s2 x).
proof. by move=> [M1] bb1 [M2] bb2; exists (M1 + M2); apply/bounded_byD. qed.

lemma boundedN s: bounded s => bounded (fun x => -(s x)).
proof. by move=> [M] bb_; exists M; apply/bounded_byN. qed.

lemma boundedB s1 s2:
  bounded s1 => bounded s2 =>
  bounded (fun x => s1 x - s2 x).
proof. by move=> [M1] bb1 [M2] bb2; exists (M1 + M2); apply/bounded_byB. qed.

lemma boundedZ c s: bounded s => bounded (fun x => c * s x).
proof. by move=> [M] bb_; exists (`|c| * M); apply/bounded_byZ. qed.

lemma boundedM s1 s2: bounded s1 => bounded s2 =>
  bounded (fun x => s1 x * s2 x).
proof. by move=> [M1] bb1 [M2] bb2; exists (M1 * M2); apply/bounded_byM. qed.

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

(* -------------------------------------------------------------------- *)
lemma cnvtopiN s: convergetopi s <=> convergetoni (fun n => - s n).
proof.
by split=> cnv_ M; case/(_ (-M)): cnv_ => N lt_; exists N;
move=> n le_; move/(_ _ le_)/ltr_oppl: lt_.
qed.

lemma cnvtoniN s: convergetoni s <=> convergetopi (fun n => - s n).
proof. by rewrite cnvtopiN -eq_iff; congr; apply/fun_ext=> ?. qed.

lemma cnvtopiD s1 s2: convergetopi s1 => convergetopi s2 =>
  convergetopi (fun x => s1 x + s2 x).
proof.
move=> cnv1 cnv2 M; case/(_ (M / 2%r)): cnv1 => N1 lt_1.
case/(_ (M / 2%r)): cnv2 => N2 lt_2; exists (max N1 N2).
move=> n /IntOrder.ler_maxrP [leN1n leN2n].
move: lt_1 lt_2 => /(_ _ leN1n) lt_1 /(_ _ leN2n) lt_2.
move: (ltr_add _ _ _ _ lt_1 lt_2); apply/ler_lt_trans.
by rewrite double_half.
qed.

lemma cnvtopiD_boundedr s1 s2: convergetopi s1 => bounded s2 =>
  convergetopi (fun x => s1 x + s2 x).
proof.
move=> cnv1 [M2] [N2 bb_] M1; case/(_ (M1 + M2)): cnv1 => N1 lt_.
exists (max N1 N2) => n /IntOrder.ler_maxrP [leN1n leN2n].
move/(_ _ leN1n): lt_; rewrite -ltr_subl_addr -!ltr_subr_addl.
by apply/ler_lt_trans; case/(_ _ leN2n)/ler_norml: bb_; move/ler_oppl.
qed.

lemma cnvtopiD_boundedl s1 s2: convergetopi s2 => bounded s1 =>
  convergetopi (fun x => s1 x + s2 x).
proof.
move=> cnv2 b1; move: (cnvtopiD_boundedr _ _ cnv2 b1).
by apply/eq_cnvtopi => n /=; apply/addrC.
qed.

lemma cnvtopiD_cnvr s1 s2: convergetopi s1 => converge s2 =>
  convergetopi (fun x => s1 x + s2 x).
proof. by move=> cnv1 /bounded_cnv; apply/cnvtopiD_boundedr. qed.

lemma cnvtopiD_cnvl s1 s2: convergetopi s2 => converge s1 =>
  convergetopi (fun x => s1 x + s2 x).
proof. by move=> cnv2 /bounded_cnv; apply/cnvtopiD_boundedl. qed.

lemma cnvtoniD s1 s2: convergetoni s1 => convergetoni s2 =>
  convergetoni (fun x => s1 x + s2 x).
proof.
move=> /cnvtoniN cnv1 /cnvtoniN cnv2; move: (cnvtopiD _ _ cnv1 cnv2).
by move/cnvtopiN; apply/eq_cnvtoni => n /=; rewrite opprD.
qed.

lemma cnvtoniD_boundedr s1 s2: convergetoni s1 => bounded s2 =>
  convergetoni (fun x => s1 x + s2 x).
proof.
move=> /cnvtoniN cnv1 /boundedN b2; move: (cnvtopiD_boundedr _ _ cnv1 b2).
by move/cnvtopiN; apply/eq_cnvtoni => n /=; rewrite opprD.
qed.

lemma cnvtoniD_boundedl s1 s2: convergetoni s2 => bounded s1 =>
  convergetoni (fun x => s1 x + s2 x).
proof.
move=> cnv2 b1; move: (cnvtoniD_boundedr _ _ cnv2 b1).
by apply/eq_cnvtoni => n /=; apply/addrC.
qed.

lemma cnvtoniD_cnvr s1 s2: convergetoni s1 => converge s2 =>
  convergetoni (fun x => s1 x + s2 x).
proof. by move=> cnv1 /bounded_cnv; apply/cnvtoniD_boundedr. qed.

lemma cnvtoniD_cnvl s1 s2: convergetoni s2 => converge s1 =>
  convergetoni (fun x => s1 x + s2 x).
proof. by move=> cnv2 /bounded_cnv; apply/cnvtoniD_boundedl. qed.

lemma cnvtopiB s1 s2:
  convergetopi s1 => convergetoni s2 =>
  convergetopi (fun x => s1 x - s2 x).
proof. by move=> cv1 /cnvtoniN cvN2; have:= (cnvtopiD _ _ cv1 cvN2); apply/eq_cnvtopi. qed.

lemma cnvtoniB s1 s2:
  convergetoni s1 => convergetopi s2 =>
  convergetoni (fun x => s1 x - s2 x).
proof. by move=> cv1 /cnvtopiN cvN2; have:= (cnvtoniD _ _ cv1 cvN2); apply/eq_cnvtoni. qed.

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
rewrite ltr_norml => -[+ _] @/F; rewrite ltr_subr_addl /F.
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


(* -------------------------------------------------------------------- *)
lemma eq_bigO_from (N : int) s1 s2 t1 t2 :
  (forall n , N <= n => s1 n = s2 n /\ t1 n = t2 n) =>
  bigO s1 t1 =>
  bigO s2 t2.
proof.
  move=> eq_; rewrite /bigO.
  apply/(eq_bounded_from N) => n leNn /=.
  by case: (eq_ _ leNn) => -> ->.
qed.

lemma bigO0 s :
  bigO s (fun _ => 0%r).
proof.
  rewrite /bigO; move: (boundedC 0%r).
  by apply/(eq_bounded_from 0) => n le0n.
qed.

lemma bigO_id s :
  (exists (N : int) , forall n , N <= n => s n <> 0%r) =>
  bigO s s.
proof.
  case=> N neq0_; rewrite /bigO; move: (boundedC 1%r).
  apply/(eq_bounded_from N) => n leNn /=.
  by rewrite divrr //; apply/neq0_.
qed.

lemma bigOD s t1 t2 :
  bigO s t1 =>
  bigO s t2 =>
  bigO s (fun n => t1 n + t2 n).
proof.
  rewrite /bigO => O1 O2; move: (boundedD _ _ O1 O2).
  apply/(eq_bounded_from 0) => n le0n /=.
  by rewrite mulrDl.
qed.

lemma bigON s t :
  bigO s t =>
  bigO s (fun n => - t n).
proof.
  rewrite /bigO => /boundedN.
  apply/(eq_bounded_from 0) => n le0n /=.
  by rewrite mulNr.
qed.

lemma bigOM s1 s2 t1 t2 :
  bigO s1 t1 =>
  bigO s2 t2 =>
  bigO (fun n => s1 n * s2 n) (fun n => t1 n * t2 n).
proof.
  rewrite /bigO => O1 O2; move: (boundedM _ _ O1 O2).
  by apply/(eq_bounded_from 0) => n le0n.
qed.

lemma bigO_sum ['a] s (P : 'a -> bool) F xs :
  all (predU (predC P) ((bigO s) \o F)) xs =>
  bigO s (fun n => Bigreal.BRA.big P (fun x => F x n) xs).
proof.
  elim: xs => [|x xs IHxs] /=.
  + move: (bigO0 s); apply/(eq_bigO_from 0) => n le0n /=.
    by rewrite Bigreal.BRA.big_nil.
  case=> + /IHxs; rewrite /predU /(\o) or_andr /predC /=.
  case=> [NPx|[Px Ox] Oxs].
  + apply/(eq_bigO_from 0) => n le0n /=.
    by rewrite Bigreal.BRA.big_cons /= NPx.
  move: (bigOD _ _ _ Ox Oxs).
  apply/(eq_bigO_from 0) => n le0n /=.
  by rewrite Bigreal.BRA.big_cons /= Px.
qed.

lemma bigO_prod ['a] (P : 'a -> bool) F G xs :
  all (fun x => !(P x) \/ bigO (F x) (G x)) xs =>
  bigO (fun n => Bigreal.BRM.big P (fun x => F x n) xs)
       (fun n => Bigreal.BRM.big P (fun x => G x n) xs).
proof.
  elim: xs => [|x xs IHxs] /=.
  + move: (bigO_id (fun _ => 1%r) _); rewrite /bigO.
    - by exists 0 => n le0n.
    apply/(eq_bounded_from 0) => n le0n /=.
    by rewrite !Bigreal.BRM.big_nil.
  case=> + /IHxs; rewrite /(\o) or_andr /=.
  case=> [NPx|[Px Ox] Oxs].
  + apply/(eq_bigO_from 0) => n le0n /=.
    by rewrite !Bigreal.BRM.big_cons /= NPx.
  move: (bigOM _ _ _ _ Ox Oxs).
  apply/(eq_bigO_from 0) => n le0n /=.
  by rewrite !Bigreal.BRM.big_cons /= Px.
qed.


(* -------------------------------------------------------------------- *)
lemma eq_smallo_from (N : int) s1 s2 t1 t2 :
  (forall n , N <= n => s1 n = s2 n /\ t1 n = t2 n) =>
  smallo s1 t1 =>
  smallo s2 t2.
proof.
  move=> eq_; rewrite /smallo.
  apply/(eq_cnvto_from N) => n leNn /=.
  by case: (eq_ _ leNn) => -> ->.
qed.

lemma smallo0 s :
  smallo s (fun _ => 0%r).
proof.
  rewrite /smallo; move: (cnvtoC 0%r).
  by apply/(eq_cnvto_from 0) => n le0n.
qed.

lemma smallo_id s :
  smallo s (fun _ => 0%r).
proof.
  rewrite /smallo; move: (cnvtoC 0%r).
  by apply/(eq_cnvto_from 0) => n le0n.
qed.

lemma smalloD s t1 t2 :
  smallo s t1 =>
  smallo s t2 =>
  smallo s (fun n => t1 n + t2 n).
proof.
  rewrite /smallo => o1 o2; move: (cnvtoD _ _ _ _ o1 o2).
  apply/(eq_cnvto_from 0) => n le0n /=.
  by rewrite mulrDl.
qed.

lemma smalloN s t :
  smallo s t =>
  smallo s (fun n => - t n).
proof.
  rewrite /smallo => /cnvtoN.
  apply/(eq_cnvto_from 0) => n le0n /=.
  by rewrite mulNr.
qed.

lemma smalloM s1 s2 t1 t2 :
  smallo s1 t1 =>
  smallo s2 t2 =>
  smallo (fun n => s1 n * s2 n) (fun n => t1 n * t2 n).
proof.
  rewrite /smallo => o1 o2; move: (cnvtoM _ _ _ _ o1 o2).
  by apply/(eq_cnvto_from 0) => n le0n.
qed.

lemma smallo_sum ['a] s (P : 'a -> bool) F xs :
  all (predU (predC P) ((smallo s) \o F)) xs =>
  smallo s (fun n => Bigreal.BRA.big P (fun x => F x n) xs).
proof.
  elim: xs => [|x xs IHxs] /=.
  + move: (smallo0 s); apply/(eq_smallo_from 0) => n le0n /=.
    by rewrite Bigreal.BRA.big_nil.
  case=> + /IHxs; rewrite /predU /(\o) or_andr /predC /=.
  case=> [NPx|[Px ox] oxs].
  + apply/(eq_smallo_from 0) => n le0n /=.
    by rewrite Bigreal.BRA.big_cons /= NPx.
  move: (smalloD _ _ _ ox oxs).
  apply/(eq_smallo_from 0) => n le0n /=.
  by rewrite Bigreal.BRA.big_cons /= Px.
qed.

lemma smallo_prod ['a] (P : 'a -> bool) F G xs :
  has P xs =>
  all (fun x => !(P x) \/ smallo (F x) (G x)) xs =>
  smallo (fun n => Bigreal.BRM.big P (fun x => F x n) xs)
         (fun n => Bigreal.BRM.big P (fun x => G x n) xs).
proof.
  elim: xs => [|x xs IHxs] //=; rewrite or_andl.
  case=> [[Px NhasPxs]|hasPxs].
  + rewrite Px /=; case=> + all_.
    apply/(eq_smallo_from 0) => n le0n /=.
    by rewrite !Bigreal.BRM.big_cons Px /= !Bigreal.BRM.big1_seq //;
    move=> ? [? mem_]; move/hasPn/(_ _ mem_): NhasPxs.
  case=> or_ all_; move: IHxs; rewrite hasPxs all_ /=; move: or_; rewrite or_andr /=.
  case=> [NPx|[Px ox] oxs].
  + apply/(eq_smallo_from 0) => n le0n /=.
    by rewrite !Bigreal.BRM.big_cons /= NPx.
  move: (smalloM _ _ _ _ ox oxs).
  apply/(eq_smallo_from 0) => n le0n /=.
  by rewrite !Bigreal.BRM.big_cons /= Px.
qed.

(* -------------------------------------------------------------------- *)
lemma smallo_bigO s t :
  smallo s t =>
  bigO s t.
proof. by apply/bounded_cnvto. qed.

lemma smallo_bigOM s1 s2 t1 t2 :
  smallo s1 t1 =>
  bigO s2 t2 =>
  smallo (fun n => s1 n * s2 n) (fun n => t1 n * t2 n).
proof.
  rewrite /smallo /bigO => o1 O2; move: (cnvtoM_boundedr _ _ o1 O2).
  by apply/(eq_cnvto_from 0) => n le0n.
qed.

lemma bigO_smalloM s1 s2 t1 t2 :
  bigO s1 t1 =>
  smallo s2 t2 =>
  smallo (fun n => s1 n * s2 n) (fun n => t1 n * t2 n).
proof.
  move=> O1 o2; move: (smallo_bigOM _ _ _ _ o2 O1).
  apply/(eq_cnvto_from 0) => n le0n.
  by rewrite /= (mulrC (s1 _)) (mulrC (t1 _)).
qed.
