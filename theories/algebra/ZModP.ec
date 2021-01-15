(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
require import Int IntDiv.
require (*--*) Subtype Ring StdOrder.
(*---*) import Ring.IntID StdOrder.IntOrder.

(* ==================================================================== *)
abstract theory ZModRing.
(* -------------------------------------------------------------------- *)
(* This abstract theory provides the construction of the ring Z/pZ.     *)
(* -------------------------------------------------------------------- *)
const p : { int | 2 <= p } as ge2_p.

(* -------------------------------------------------------------------- *)
type zmod.

clone Subtype as Sub with
  type T <- int, type sT <- zmod,
  pred P (x : int) <- 0 <= x < p.

(* -------------------------------------------------------------------- *)
op inzmod (z : int)  = Sub.insubd (z %% p).
op asint  (z : zmod) = Sub.val z.

lemma inzmodK (z : int): asint (inzmod z) = z %% p.
proof. smt ml=1. qed.

lemma asint_inj: injective asint by apply/Sub.val_inj.

lemma ge0_asint x : 0 <= asint x.
proof. by case: (Sub.valP x). qed.

lemma gtp_asint x : asint x < p.
proof. by case: (Sub.valP x). qed.

lemma rg_asint x : 0 <= asint x < p.
proof. by rewrite ge0_asint gtp_asint. qed.

lemma asintK x : inzmod (asint x) = x.
proof. by rewrite /inzmod pmod_small 1:rg_asint /insubd Sub.valK. qed.

(* -------------------------------------------------------------------- *)
abbrev zmodcgr (z1 z2 : int) = z1 %% p = z2 %% p.

(* -------------------------------------------------------------------- *)
lemma eq_inzmod (z1 z2 : int) : zmodcgr z1 z2 <=> inzmod z1 = inzmod z2.
proof. split.
+ by move=> h; apply/asint_inj; rewrite !inzmodK.
+ by move/(congr1 asint); rewrite !inzmodK.
qed.

(* -------------------------------------------------------------------- *)
lemma asint_eq (z1 z2 : zmod) : (asint z1 = asint z2) <=> (z1 = z2).
proof. by split=> [/asint_inj|->//]. qed.

(* -------------------------------------------------------------------- *)
op zero      = inzmod 0.
op one       = inzmod 1.
op [ - ] x   = inzmod (- asint x).
op ( + ) x y = inzmod (asint x + asint y).
op ( * ) x y = inzmod (asint x * asint y).

op unit x = exists y, y * x = one.
op inv  x = choiceb (fun y => y * x = one) x.

abbrev (-) x y = x + -y.
abbrev (/) x y = x * inv y.

(* -------------------------------------------------------------------- *)
lemma zeroE: asint zero = 0.
proof. by rewrite /zero inzmodK mod0z. qed.

lemma oneE: asint one = 1.
proof. by rewrite /one inzmodK modz_small; smt. qed.

lemma oppE (x : zmod): asint (-x) = (- (asint x)) %% p.
proof. by rewrite /[-] /inzmod /asint /= Sub.insubdK; smt. qed.

lemma addE (x y : zmod): asint (x + y) = (asint x + asint y) %% p.
proof. by rewrite /(+) /inzmod /asint /= Sub.insubdK; smt. qed.

lemma mulE (x y : zmod): asint (x * y) = (asint x * asint y) %% p.
proof. rewrite /( * ) /inzmod /asint /= Sub.insubdK; smt. qed.

(* -------------------------------------------------------------------- *)
theory ZModule.
lemma addrA (x y z : zmod): x + (y + z) = (x + y) + z.
proof. by apply/asint_inj; rewrite !addE modzDml modzDmr addzA. qed.

lemma addrC (x y : zmod): x + y = y + x.
proof. by apply/asint_inj; rewrite !addE addzC. qed.

lemma add0r (x : zmod): zero + x = x.
proof. by apply/asint_inj; rewrite !(addE, zeroE) add0z smt. qed.

lemma addNr (x : zmod): (-x) + x = zero.
proof.
apply/asint_inj; rewrite !(zeroE, addE, oppE).
by rewrite modzDml addNz.
qed.
end ZModule.

(* -------------------------------------------------------------------- *)
theory ComRing.
lemma oner_neq0 : one <> zero by smt.

lemma mulrA (x y z : zmod): x * (y * z) = (x * y) * z.
proof. by apply/asint_inj; rewrite !mulE modzMml modzMmr mulzA. qed.

lemma mulrC (x y : zmod): x * y = y * x.
proof. by apply/asint_inj; rewrite !mulE mulzC. qed.

lemma mul1r (x : zmod): one * x = x.
proof. by apply/asint_inj; rewrite !(mulE, oneE) mul1z smt. qed.

lemma mulrDl (x y z : zmod): (x + y) * z = (x * z) + (y * z).
proof.
apply/asint_inj; rewrite !(addE, mulE).
by rewrite !(modzMml, modzMmr, modzDml, modzDmr) mulzDl.
qed.

lemma mulVr x : unit x => (inv x) * x = one.
proof. by move/choicebP=> /(_ x). qed.

lemma unitP x y : y * x = one => unit x.
proof. by move=> eq; exists y. qed.

lemma unitout x : ! unit x => inv x = x.
proof.
move=> Nux; rewrite /inv choiceb_dfl //= => y; apply/negP.
by move=> h; apply/Nux; exists y.
qed.
end ComRing.

(* -------------------------------------------------------------------- *)
clone import Ring.ComRing as ZModpRing with
  type t     <- zmod,
  op   zeror <- zero,
  op   oner  <- one,
  op   ( + ) <- ( + ),
  op   [ - ] <- ([-]),
  op   ( * ) <- ( * ),
  op   invr  <- inv,
  pred unit  <- unit
  proof *.

realize addrA.     proof. by apply/ZModule.addrA. qed.
realize addrC.     proof. by apply/ZModule.addrC. qed.
realize add0r.     proof. by apply/ZModule.add0r. qed.
realize addNr.     proof. by apply/ZModule.addNr. qed.
realize mulrA.     proof. by apply/ComRing.mulrA. qed.
realize mulrC.     proof. by apply/ComRing.mulrC. qed.
realize mul1r.     proof. by apply/ComRing.mul1r. qed.
realize mulrDl.    proof. by apply/ComRing.mulrDl. qed.
realize oner_neq0. proof. by apply/ComRing.oner_neq0. qed.
realize mulVr.     proof. by apply/ComRing.mulVr. qed.
realize unitP.     proof. by apply/ComRing.unitP. qed.
realize unitout.   proof. by apply/ComRing.unitout. qed.

(* -------------------------------------------------------------------- *)
instance ring with zmod
  op rzero = ZModRing.zero
  op rone  = ZModRing.one
  op add   = ZModRing.( + )
  op mul   = ZModRing.( * )
  op opp   = ZModRing.([-])

  proof oner_neq0 by apply/ZModpRing.oner_neq0
  proof addr0     by apply/ZModpRing.addr0
  proof addrA     by apply/ZModpRing.addrA
  proof addrC     by apply/ZModpRing.addrC
  proof addrN     by apply/ZModpRing.addrN
  proof mulr1     by apply/ZModpRing.mulr1
  proof mulrA     by apply/ZModpRing.mulrA
  proof mulrC     by apply/ZModpRing.mulrC
  proof mulrDl    by apply/ZModpRing.mulrDl.

(* -------------------------------------------------------------------- *)
lemma inzmodD (a b : int):
  inzmod (a + b) = inzmod a + inzmod b.
proof. by apply/asint_inj; rewrite addE !inzmodK modzDmr modzDml. qed.

lemma inzmodM (a b : int):
  inzmod (a * b) = inzmod a * inzmod b.
proof. by apply/asint_inj; rewrite mulE !inzmodK modzMmr modzMml. qed.

lemma inzmodN (n : int):
  inzmod (- n) = -(inzmod n).
proof. by apply/asint_inj; rewrite oppE !inzmodK modzNm. qed.

lemma inzmodB (a b : int):
  inzmod (a - b) = (inzmod a) + (- (inzmod b)).
proof. by rewrite inzmodD inzmodN. qed.

(* -------------------------------------------------------------------- *)
lemma intmul_asint (x : zmod) : x = intmul one (asint x).
proof.
rewrite /intmul ltrNge ge0_asint /= AddMonoid.iteropE -{1}(asintK x).
elim: (asint x) (ge0_asint x) => [|i ge0_i ih]; first by rewrite iter0.
by rewrite iterS //= inzmodD -ih addrC.
qed.
end ZModRing.

(* ==================================================================== *)
abstract theory ZModField.

const p : { int | prime p } as prime_p.

clone include ZModRing with
  op    p <- p
  proof ge2_p by smt(gt1_prime prime_p).

lemma unitE (x : zmod) : (unit x) <=> (x <> zero).
proof.
split; first by apply: contraL => ->; apply: ZModpRing.unitr0.
move=> nz_x; exists (inzmod (invm (asint x) p)).
apply: asint_inj; rewrite oneE mulE inzmodK.
rewrite (@modzE (invm _ _)) -mulNr mulrDl mulrAC modzMDr mulrC.
apply/mulmV; first by apply/prime_p.
by move: nz_x; rewrite -asint_eq zeroE pmod_small // rg_asint.
qed.

clone import Ring.Field as ZModpField with
  type t     <- zmod,
  op   zeror <- zero,
  op   oner  <- one,
  op   ( + ) <- ( + ),
  op   [ - ] <- ([-]),
  op   ( * ) <- ( * ),
  op   invr  <- inv
  proof *.

realize addrA.     proof. by apply/ZModule.addrA. qed.
realize addrC.     proof. by apply/ZModule.addrC. qed.
realize add0r.     proof. by apply/ZModule.add0r. qed.
realize addNr.     proof. by apply/ZModule.addNr. qed.
realize mulrA.     proof. by apply/ComRing.mulrA. qed.
realize mulrC.     proof. by apply/ComRing.mulrC. qed.
realize mul1r.     proof. by apply/ComRing.mul1r. qed.
realize mulrDl.    proof. by apply/ComRing.mulrDl. qed.
realize oner_neq0. proof. by apply/ComRing.oner_neq0. qed.

realize mulVr.
proof. by move=> x nz_x; rewrite &(ComRing.mulVr) unitE. qed.

realize unitP.
proof. by move=> x y h; rewrite -unitE &(ComRing.unitP _ y). qed.

realize unitout.
proof. by move=> x; rewrite -unitE &(ComRing.unitout). qed.

realize mulf_eq0.
proof.                          (* FIXME: should be generic *)
move=> x y; case: (x = zero) => //= [->|]; first by rewrite ZModpRing.mul0r.
move=> nz_x; split=> [|->]; last by rewrite ZModpRing.mulr0.
move=> h; apply: (ZModpRing.mulrI x); last by rewrite ZModpRing.mulr0.
by rewrite unitE.
qed.

(* -------------------------------------------------------------------- *)
instance field with zmod
  op rzero = ZModField.zero
  op rone  = ZModField.one
  op add   = ZModField.( + )
  op mul   = ZModField.( * )
  op opp   = ZModField.([-])
  op inv   = ZModField.inv
  op expr  = ZModField.ZModpField.exp

  proof oner_neq0 by apply/ZModpField.oner_neq0
  proof addr0     by apply/ZModpField.addr0
  proof addrA     by apply/ZModpField.addrA
  proof addrC     by apply/ZModpField.addrC
  proof addrN     by apply/ZModpField.addrN
  proof mulr1     by apply/ZModpField.mulr1
  proof mulrA     by apply/ZModpField.mulrA
  proof mulrC     by apply/ZModpField.mulrC
  proof mulrDl    by apply/ZModpField.mulrDl
  proof mulrV     by apply/ZModpField.mulrV
  proof expr0     by apply/ZModpField.expr0
  proof exprS     by apply/ZModpField.exprS
  proof exprN     by (move=> ?? _; apply/ZModpField.exprN).
end ZModField.
