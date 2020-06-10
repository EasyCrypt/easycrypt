(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
require import AllCore Ring StdRing.
require (*--*) Number.
(*---*) import IntID.

(* -------------------------------------------------------------------- *)
theory IntOrder.
clone include Number.RealDomain
  with type t <- int,

  pred Domain.unit (z : int) <- (z = 1 \/ z = -1),
  op   Domain.zeror  <- 0,
  op   Domain.oner   <- 1,
  op   Domain.( + )  <- Int.( + ),
  op   Domain.([-])  <- Int.([-]),
  op   Domain.( * )  <- Int.( * ),
  op   Domain.invr   <- (fun (z : int) => z),
  op   Domain.intmul <- IntID.intmul,
  op   Domain.ofint  <- IntID.ofint_id,
  op   Domain.exp    <- IntID.exp,
  op   minr          <- min,
  op   maxr          <- max,

  op   "`|_|" <- Int."`|_|",
  op   ( <= ) <- Int.(<=),
  op   ( <  ) <- Int.(< )

  proof Domain.* by smt, Axioms.* by smt

  remove abbrev Domain.(-)
  remove abbrev Domain.(/).

(* -------------------------------------------------------------------- *)
op signz (z : int) = (exp (-1) (b2i (z < 0))) * (b2i (z <> 0)).

lemma signzE z : z = (signz z) * `|z|.
proof.
rewrite /signz; case: (z = 0) => [->|]; 1: by rewrite normr0.
move=> nz_z; rewrite mulr1; case: (z < 0); rewrite (expr0, expr1).
  by move=> /ltr0_norm => ->; rewrite mulN1r opprK.
by rewrite ltrNge => /= /ger0_norm => ->.
qed.

lemma signzN (z : int) : signz (-z) = - (signz z).
proof.
rewrite /signz oppr_eq0; case: (z = 0) => //= nz_z.
rewrite b2i1 /= oppr_lt0 ltrNge ler_eqVlt nz_z /=.
by case: (z < 0) => //=; rewrite !(expr0, expr1).
qed.

lemma signz0 : signz 0 = 0.
proof. by rewrite /signz ltrr. qed.

lemma signz_gt0 (z : int) : 0 < z => signz z = 1.
proof.
move=> gt0_z; rewrite /signz (gtr_eqF z) // b2i1 /=.
by rewrite ltrNge ltrW // b2i0 expr0.
qed.

lemma signz_lt0 (z : int) : z < 0 => signz z = -1.
proof.
by move=> lt0_z; rewrite -(opprK z) signzN signz_gt0 ?oppr_gt0.
qed.

lemma signVzE (z : int) : `|z| = (signz z) * z.
proof.
rewrite {3}(signzE) mulrA /signz; case: (z = 0).
  by move=> ->; rewrite normr0.
move=> nz_0; rewrite b2i1 /= -{1}(mul1r `|z|); congr.
rewrite -exprDn ?b2i_ge0 -signr_odd ?addr_ge0 ?b2i_ge0.
by rewrite -mul1r2z oddM /ofint_id intmulz odd2 expr0.
qed.
end IntOrder.

(* -------------------------------------------------------------------- *)
clone Number.RealField as RealOrder
  with type t <- real,

  op   Field.zeror  <- 0%r,
  op   Field.oner   <- 1%r,
  op   Field.( + )  <- Real.( + ),
  op   Field.([-])  <- Real.([-]),
  op   Field.( * )  <- Real.( * ),
  op   Field.invr   <- Real.inv,
  op   Field.intmul <- RField.intmul,
  op   Field.ofint  <- RField.ofint,
  op   Field.exp    <- RField.exp,
  op   minr          = fun x y : real => if x <= y then x else y,
  op   maxr          = fun x y : real => if y <= x then x else y,

  op   "`|_|" <- Real."`|_|",
  op   ( <= ) <- Real.(<=),
  op   ( <  ) <- Real.(< )

  proof Field.* by smt, Axioms.* by smt full

  remove abbrev Field.(-)
  remove abbrev Field.(/).
