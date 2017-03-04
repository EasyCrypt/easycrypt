(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2017 - Inria
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
require import Bool Option Fun Distr Int IntExtra Real RealExtra.
require import StdRing StdOrder.
(*---*) import RField RealOrder.

pragma +implicits.

(* -------------------------------------------------------------------- *)
op convexe (f : real -> real) (a b : real) =
  forall d, 0%r <= d <= 1%r =>
     f (d * a + (1%r - d) * b) <= d * f a + (1%r - d) * f b.

lemma nosmt segment_coeff (a b x : real) : a <= x <= b =>
  exists d, 0%r <= d <= 1%r /\ x = d * a + (1%r - d) * b.
proof.
move=> x_in_ab; case (b - a = 0%r)=> [/# | nz_aBb].
exists (1%r - (x-a)/(b-a)); split; last by fieldeq.
by rewrite subr_ge0 ler_pdivr_mulr /#.
qed.

lemma convexe_le f a b x :
  convexe f a b => a <= x <= b => f x <= maxr (f a) (f b).
proof.
move=> cvx_f /segment_coeff [d] [d_in_01 ->].
have /ler_trans := cvx_f d d_in_01; apply.
pose z := maxr (f a) (f b); pose Z := (d * z + (1%r - d) * z).
apply/(ler_trans Z); [rewrite /Z /z | smt ()].
by apply/ler_add; apply/ler_wpmul2l; smt (maxrl maxrr).
qed.

lemma convexeC c a b: convexe (fun _ => c) a b.
proof. smt (). qed.

lemma convexe_id a b: convexe (fun x => x) a b.
proof. smt (). qed.

lemma convexeD f1 f2 a b:
  convexe f1 a b => convexe f2 a b => convexe (fun x => f1 x + f2 x) a b.
proof. smt (). qed.

lemma convexeZ c f a b: 0%r <= c =>
  convexe f a b => convexe (fun x => c * f x) a b.
proof.
move=> ge0_x cvx_f d d_in_01; rewrite mulrCA (mulrCA (1%r - _)).
by rewrite -mulrDr; apply/ler_wpmul2l=> //; apply/cvx_f.
qed.
