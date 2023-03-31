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
  op   Domain.lreg   <- IntID.lreg,
  op   minr          <- min,
  op   maxr          <- max,

  op   "`|_|" <- Int."`|_|",
  op   ( <= ) <- Int.(<=),
  op   ( <  ) <- Int.(< )

  proof Domain.* by smt(invr0), Axioms.* by smt()

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
rewrite -exprD_nneg ?b2i_ge0 -signr_odd ?addr_ge0 ?b2i_ge0.
by rewrite -mul1r2z oddM /ofint_id intmulz odd2 expr0.
qed.

lemma signz_proj (z : int) : signz (signz z) = signz z.
proof.
rewrite /signz /b2i; case (z < 0); [|case (z <> 0)]; move => //=.
+ by move => ltz0; rewrite (ltr_eqF z) //= !expr1.
by rewrite -lerNgt ler_eqVlt eq_sym => -> /= lt0z; rewrite !expr0.
qed.

lemma signz_norm (z : int) : signz (`|z|) = b2i (z <> 0).
proof. by rewrite /signz /b2i normr_lt0 normr0P expr0. qed.

lemma signzM (a b : int) : signz (a * b) = signz a * signz b.
proof.
case (a < 0) => [lta0|/lerNgt/ler_eqVlt [<<-|lt0a]];
(case (b < 0) => [ltb0|/lerNgt/ler_eqVlt [<<-|lt0b]] //=).
+ by rewrite signz_gt0 ?nmulr_rgt0 // !signz_lt0.
+ by rewrite signz_lt0 ?nmulr_rlt0 // signz_lt0 // signz_gt0.
+ by rewrite signz_lt0 ?pmulr_rlt0 // signz_gt0 // signz_lt0.
by rewrite signz_gt0 ?pmulr_rgt0 // !signz_gt0.
qed.

lemma signz_eq0 a :
  signz a = 0 <=> a = 0.
proof.
case (a < 0) => [lta0|/lerNgt/ler_eqVlt [<<-|lt0a]].
+ by rewrite signz_lt0 //= ltr_eqF.
+ by rewrite signz0.
by rewrite signz_gt0 //= gtr_eqF.
qed.

lemma signz_eq1 a :
  signz a = 1 <=> 0 < a.
proof.
case (a < 0) => [lta0|/lerNgt/ler_eqVlt [<<-|lt0a]].
+ by rewrite signz_lt0 //= -lerNgt ltzW.
+ by rewrite signz0.
by rewrite lt0a signz_gt0.
qed.

lemma signz_eqN1 a :
  signz a = -1 <=> a < 0.
proof.
case (a < 0) => [lta0|/lerNgt/ler_eqVlt [<<-|lt0a]].
+ by rewrite signz_lt0.
+ by rewrite signz0.
by rewrite signz_gt0.
qed.

lemma signz_normr_bij a b :
  (signz a = signz b /\ `|a| = `|b|) <=> (a = b).
proof.
split => [|<<-//]; case (a < 0) => [lta0|/lerNgt/ler_eqVlt [<<-|lt0a]].
+ rewrite signz_lt0 // eq_sym signz_eqN1 => -[ltb0].
  by rewrite !ltr0_norm //; apply/oppr_inj.
+ by rewrite signz0 eq_sym signz_eq0 => -[->>].
rewrite signz_gt0 // eq_sym signz_eq1 => -[lt0b].
by rewrite !gtr0_norm.
qed.

end IntOrder.

(* -------------------------------------------------------------------- *)
theory RealOrder. 
clone include Number.RealField
  with type Field.t <- real,

  op   Field.zeror  <- 0%r,
  op   Field.oner   <- 1%r,
  op   Field.( + )  <- Real.( + ),
  op   Field.([-])  <- Real.([-]),
  op   Field.( * )  <- Real.( * ),
  op   Field.invr   <- Real.inv,
  pred Field.unit   <- (fun x => x <> 0%r),
  op   Field.intmul <- RField.intmul,
  op   Field.ofint  <- RField.ofint,
  op   Field.exp    <- RField.exp,
  op   Field.lreg   <- RField.lreg,
  op   minr          = fun x y : real => if x <= y then x else y,
  op   maxr          = fun x y : real => if y <= x then x else y,

  op   "`|_|" <- Real."`|_|",
  op   ( <= ) <- Real.(<=),
  op   ( <  ) <- Real.(< )

  proof Field.* by smt(RField.invr0), Axioms.* by smt()

  remove abbrev Field.(-)
  remove abbrev Field.(/).

(* This is used by the upto tactic *)
lemma upto_maxr (E1 E1b E1nb E2 E2b E2nb E1b' E2b' : real) :
  E1 = E1b + E1nb =>
  E2 = E2b + E2nb =>
  E1nb = E2nb =>
  0.0 <= E1b => 
  E1b <= E1b' =>
  0.0 <= E2b => 
  E2b <= E2b' =>
  `| E1 - E2 | <= maxr E1b' E2b'.
proof. 
  move=> h1 h2 h3 h4 h5 h6 h7.
  apply (ler_trans `|E1b - E2b|); 1: by apply (upto_abs _ _ _ _ _ _ h1 h2 h3).
  apply (ler_trans (maxr E1b E2b)); 1: by apply (ler_norm_maxr _ _ h4 h6).
  by apply ler_maxr_trans.
qed.

end RealOrder.
