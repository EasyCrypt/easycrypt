(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2015 - IMDEA Software Institute
 * Copyright (c) - 2012--2015 - Inria
 * 
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
require import Bool Option Fun Distr Int IntExtra Real RealExtra.
require import StdRing StdOrder StdBigop List Array.
(*---*) import IterOp BRA IntOrder.

pragma +implicits.

(* -------------------------------------------------------------------- *)
pred convergeto (s : int -> real) (x : real) =
  forall epsilon, 0%r <= epsilon => exists N,
    forall n, (N <= n)%Int => `|s n - x| < epsilon.

pred converge (s : int -> real) =
  exists l, convergeto s l.

pred bounded_by (s : int -> real) (M : real) =
  exists N, forall n, (N <= n)%Int => `|s n| <= M.

pred bounded (s : int -> real) =
  exists M, bounded_by s M.

pred monotone (s : int -> real) =
  forall n, 0 <= n => s n <= s (n+1).

(* -------------------------------------------------------------------- *)
lemma monotoneP (s : int -> real):
  monotone s <=> (forall m n, 0 <= m <= n => s m <= s n).
proof. admit. qed.

lemma uniq_cnv s x y: convergeto s x => convergeto s y => x = y.
proof. admit. qed.

lemma eq_cnv s1 s2 l:
     (exists N, forall n, (N <= n)%Int => s1 n = s2 n)
  => convergeto s1 l => convergeto s2 l.
proof. admit. qed.

lemma le_cnv s1 s2 l1 l2:
     (exists N, forall n, (N <= n)%Int => (s1 n <= s2 n)%Real)
  => convergeto s1 l1 => convergeto s2 l2 => l1 <= l2.
proof. admit. qed.

lemma cnvC c: convergeto (fun x => c) c.
proof. admit. qed.

lemma cnvD s1 s2 l1 l2: convergeto s1 l1 => convergeto s2 l2 =>
  convergeto (fun x => s1 x + s2 x) (l1 + l2).
proof. admit. qed.

lemma cnvB s l: convergeto s l => convergeto (fun x => -(s x)) (-l).
proof. admit. qed.

lemma cnvM s1 s2 l1 l2: convergeto s1 l1 => convergeto s2 l2 =>
  convergeto (fun x => s1 x * s2 x) (l1 * l2).
proof. admit. qed.

lemma cnvZ c s l: convergeto s l => convergeto (fun x => c * s x) l.
proof. admit. qed.

lemma cnvM_bounded s1 s2: convergeto s1 0%r => bounded s2 => 
  convergeto (fun x => s1 x * s2 x) 0%r.
proof. admit. qed.

(* -------------------------------------------------------------------- *)
op lim (s : int -> real) : real.

axiom limP (s : int -> real): converge s <=> convergeto s (lim s).
axiom lim_Ncnv (s : int -> real): ! converge s => lim s = 0%r.
