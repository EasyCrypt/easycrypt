(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2015 - IMDEA Software Institute
 * Copyright (c) - 2012--2015 - Inria
 * 
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
require import Bool Option Fun Distr Int IntExtra Real RealExtra.
require import Ring StdRing StdOrder StdBigop List.
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
lemma monotoneP (s : int -> real):
  monotone s <=> (forall m n, 0 <= m <= n => s m <= s n).
proof.
split=> [h m n|h n]; last first.
  by move=> ge0n; apply/h; rewrite ge0n ler_addl.
case=> ge0m; rewrite -IntOrder.subr_ge0 -{2}(@IntID.subrK n m).
rewrite addrC; elim: (n - m)=> //.
by move=> i ge0i ih; rewrite addrA (ler_trans _ ih) // h ?addr_ge0.
qed.

lemma uniq_cnv s x y: convergeto s x => convergeto s y => x = y.
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

lemma eq_cnv N s1 s2 l:
     (forall n, (N <= n)%Int => s1 n = s2 n)
  => convergeto s1 l => convergeto s2 l.
proof.
move=> eq_s lim_s1 e gt0_e; case: (lim_s1 _ gt0_e).
move=> Ns lim_s1N; exists (max N Ns)=> n /geq_max [leN leNs].
by rewrite -eq_s // lim_s1N.
qed.

lemma eq_cnvP N s1 s2 l:
     (forall n, (N <= n)%Int => s1 n = s2 n)
  => convergeto s1 l <=> convergeto s2 l.
proof.
move=> eq; split; apply/(eq_cnv N)=> // n leNn.
by rewrite eq_sym eq.
qed.

lemma le_cnv s1 s2 l1 l2:
     (exists N, forall n, (N <= n)%Int => (s1 n <= s2 n)%Real)
  => convergeto s1 l1 => convergeto s2 l2 => l1 <= l2.
proof. admit. qed.

lemma cnvC c: convergeto (fun x => c) c.
proof. by move=> e gt0e; exists 0 => n _; rewrite subrr normr0. qed.

lemma cnvD s1 s2 l1 l2: convergeto s1 l1 => convergeto s2 l2 =>
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

lemma cnvN s l: convergeto s l => convergeto (fun x => -(s x)) (-l).
proof.
move=> cnv e /cnv [N {cnv} cnv]; exists N => n /cnv h.
by rewrite subrE -opprD normrN -subrE.
qed.

lemma cnvZ c s l: convergeto s l => convergeto (fun x => c * s x) (c * l).
proof.
move=> cnv e gt0e; case: (c = 0%r) => [->|nz_c].
  by exists 0 => n _ /=; rewrite normr0.
have: 0%r < e / `|c| by rewrite divr_gt0 // normr_gt0.
move/cnv=> [N {cnv} cnv]; exists N => n /cnv.
rewrite -mulrBr normrM -(@ltr_pmul2l `|c|) ?normr_gt0 //.
by rewrite divrE mulrCA mulrV 1:normr0P.
qed.

lemma cnvM s1 s2 l1 l2: convergeto s1 l1 => convergeto s2 l2 =>
  convergeto (fun x => s1 x * s2 x) (l1 * l2).
proof. admit. qed.

lemma cnvM_bounded s1 s2: convergeto s1 0%r => bounded s2 => 
  convergeto (fun x => s1 x * s2 x) 0%r.
proof. admit. qed.
  
(* -------------------------------------------------------------------- *)
op lim (s : int -> real) =
  choiceb (fun l => convergeto s l) 0%r.

(* -------------------------------------------------------------------- *)
lemma limP (s : int -> real):
  converge s <=> convergeto s (lim s).
proof. by split=> [/choicebP /(_ 0%r)|lims]; last exists (lim s). qed.

lemma lim_Ncnv (s : int -> real):
  ! converge s => lim s = 0%r.
proof. by move=> h; apply/choiceb_dfl/for_ex. qed.

lemma lim_eq (N : int) (s1 s2 : int -> real):
     (forall n, N <= n => s1 n = s2 n)
  => lim s1 = lim s2.
proof. admit. qed.

(* -------------------------------------------------------------------- *)
lemma limC_eq_from (N : int) c (s : int -> real) :
   (forall n, N <= n => s n = c) => lim s = c.
proof. admit. qed.

lemma limC_eq c (s : int -> real) :
 (forall n, 0 <= n => s n = c) => lim s = c.
proof. by apply/limC_eq_from. qed.

lemma limC c : lim (fun x => c) = c.
proof. by apply/limC_eq. qed.
