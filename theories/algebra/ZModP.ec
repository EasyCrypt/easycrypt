(* -------------------------------------------------------------------- *)
require import AllCore List Distr Int IntDiv.
require (*--*) Bigalg Subtype Ring StdOrder.
(*---*) import Ring.IntID StdOrder.IntOrder.

(* ==================================================================== *)
abstract theory ZModRing.
(* -------------------------------------------------------------------- *)
(* This abstract theory provides the construction of the ring Z/pZ.     *)
(* -------------------------------------------------------------------- *)
const p : { int | 2 <= p } as ge2_p.

(* -------------------------------------------------------------------- *)
subtype zmod as Sub = { x : int | 0 <= x < p }.

realize inhabited.
proof. by exists 0; smt(ge2_p). qed.

(* -------------------------------------------------------------------- *)
op inzmod (z : int)  = Sub.insubd (z %% p).
op asint  (z : zmod) = Sub.val z.

lemma inzmodK (z : int): asint (inzmod z) = z %% p.
proof.
rewrite /asint /inzmod Sub.insubdK //.
rewrite modz_ge0 /= 1:&(gtr_eqF); first by smt(ge2_p).
by apply: ltz_pmod; smt(ge2_p).
qed.

lemma inzmod_mod z :
  inzmod z = inzmod (z %% p).
proof. by rewrite /inzmod modz_mod. qed.

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
proof. by rewrite /one inzmodK modz_small; smt(ge2_p). qed.

lemma oppE (x : zmod): asint (-x) = (- (asint x)) %% p.
proof. by rewrite /[-] /inzmod /asint /= Sub.insubdK; smt(ge2_p). qed.

lemma addE (x y : zmod): asint (x + y) = (asint x + asint y) %% p.
proof. by rewrite /(+) /inzmod /asint /= Sub.insubdK; smt(ge2_p). qed.

lemma mulE (x y : zmod): asint (x * y) = (asint x * asint y) %% p.
proof. rewrite /( * ) /inzmod /asint /= Sub.insubdK; smt(ge2_p). qed.

(* -------------------------------------------------------------------- *)
theory ZModule.
lemma addrA (x y z : zmod): x + (y + z) = (x + y) + z.
proof. by apply/asint_inj; rewrite !addE modzDml modzDmr addzA. qed.

lemma addrC (x y : zmod): x + y = y + x.
proof. by apply/asint_inj; rewrite !addE addzC. qed.

lemma add0r (x : zmod): zero + x = x.
proof. 
by apply/asint_inj; rewrite !(addE, zeroE) add0z; smt(rg_asint pmod_small ge2_p).
qed.

lemma addNr (x : zmod): (-x) + x = zero.
proof.
apply/asint_inj; rewrite !(zeroE, addE, oppE).
by rewrite modzDml addNz.
qed.
end ZModule.

(* -------------------------------------------------------------------- *)
theory ComRing.
lemma oner_neq0 : one <> zero.
proof. by rewrite -eq_inzmod #smt:(ge2_p). qed.

lemma mulrA (x y z : zmod): x * (y * z) = (x * y) * z.
proof. by apply/asint_inj; rewrite !mulE modzMml modzMmr mulzA. qed.

lemma mulrC (x y : zmod): x * y = y * x.
proof. by apply/asint_inj; rewrite !mulE mulzC. qed.

lemma mul1r (x : zmod): one * x = x.
proof.  apply/asint_inj; rewrite !(mulE, oneE) mul1z; smt(rg_asint). qed.

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
  type t     <= zmod,
  op   zeror <= zero,
  op   oner  <= one,
  op   ( + ) <= ( + ),
  op   [ - ] <= ([-]),
  op   ( * ) <= ( * ),
  op   invr  <= inv,
  pred unit  <= unit
  proof *

  remove abbrev (-)
  remove abbrev (/).

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

clone import Bigalg.BigComRing as BigZMod with
  theory CR <- ZModpRing
proof *.

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
lemma inzmodD_mod (a b : int):
  inzmod ((a + b) %% p) = inzmod a + inzmod b.
proof. by rewrite -inzmod_mod inzmodD. qed.

lemma inzmodM_mod (a b : int):
  inzmod ((a * b) %% p) = inzmod a * inzmod b.
proof. by rewrite -inzmod_mod inzmodM. qed.

lemma inzmodN_mod (n : int):
  inzmod ((- n) %% p) = -(inzmod n).
proof. by rewrite -inzmod_mod inzmodN. qed.

lemma inzmodB_mod (a b : int):
  inzmod ((a - b) %% p) = (inzmod a) + (- (inzmod b)).
proof. by rewrite -inzmod_mod inzmodB. qed.

(* -------------------------------------------------------------------- *)
lemma zmodcgrP (i j : int) : zmodcgr i j <=> p %| (i - j).
proof. by rewrite dvdzE -[0](mod0z p) !eq_inzmod inzmodB subr_eq0. qed.

lemma inzmod_eq0P (i : int) : inzmod i = zero <=> p %| i.
proof. by rewrite -[zero]asintK zeroE -eq_inzmod zmodcgrP. qed.

(* -------------------------------------------------------------------- *)
lemma intmul_asint (x : zmod) : x = intmul one (asint x).
proof.
rewrite /intmul ltrNge ge0_asint /= AddMonoid.iteropE -{1}(asintK x).
elim: (asint x) (ge0_asint x) => [|i ge0_i ih]; first by rewrite iter0.
by rewrite iterS //= inzmodD -ih addrC.
qed.

(* -------------------------------------------------------------------- *)
lemma inzmodW (P : zmod -> bool) :
  (forall i, 0 <= i < p => P (inzmod i)) => forall n, P n.
proof. by move=> ih n; rewrite -(asintK n) &(ih) rg_asint. qed.

(* -------------------------------------------------------------------- *)
theory DZmodP.
clone include MFinite with
  type t <- zmod,
    op Support.enum = map inzmod (range 0 p)

  proof *.

realize Support.enum_spec.
proof.
elim/inzmodW=> i rgi; rewrite count_uniq_mem; last first.
- by apply/b2i_eq1; apply/mapP; exists i=> /=; rewrite mem_range.
rewrite &(map_inj_in_uniq) -1:range_uniq // => m n.
rewrite !mem_range => rgm rgn /(congr1 asint).
by rewrite !inzmodK !pmod_small.
qed.

require import DInterval.

lemma cardE : Support.card = p.
proof. by rewrite /Support.card size_map size_range; smt(ge2_p). qed.

lemma dzmodE : dunifin = dmap [0..p-1] inzmod.
proof.
apply/eq_distr; elim/inzmodW => i rgi.
rewrite dunifin1E cardE dmapE /pred1 /(\o) /=.
rewrite -(mu_eq_support _ (pred1 i)) => /= [j /supp_dinter|].
- rewrite ler_subr_addl (addzC 1) -ltzE /pred1 => rgj.
  by rewrite -eq_inzmod !pmod_small.
- by rewrite dinter1E ler_subr_addl (addzC 1) -ltzE rgi.
qed.
end DZmodP.

end ZModRing.

(* ==================================================================== *)
abstract theory ZModField.

const p : { int | prime p } as prime_p.

clone include ZModRing with
  op    p <- p
  proof ge2_p by smt(gt1_prime prime_p).

import BigZMod.
import BMul.

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
  op   invr  <- inv,
  op   exp   <- ZModpRing.exp
  proof *
  remove abbrev (-)
  remove abbrev (/).

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

abbrev exp = ZModpRing.exp.

(* -------------------------------------------------------------------- *)
instance field with zmod
  op rzero = ZModField.zero
  op rone  = ZModField.one
  op add   = ZModField.( + )
  op mul   = ZModField.( * )
  op opp   = ZModField.([-])
  op inv   = ZModField.inv
  op expr  = ZModpRing.exp

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

(* -------------------------------------------------------------------- *)
lemma exp_inzmod m n :
  exp (inzmod m) n =
  if 0 <= n
  then inzmod (exp m n)
  else inv (inzmod (exp m (-n))).
proof.
  case: (0 <= n) => [|/ltzNge].
  + elim: n => [|n le0n]; [by rewrite !expr0|].
    by rewrite exprS // exprS // inzmodM => ->.
  rewrite -oppr_gt0 => /ltzW le0Nn.
  rewrite -(Ring.IntID.opprK n) exprN opprK.
  apply congr1; move: (-n) le0Nn => {n} n.
  elim n => [|n le0n]; [by rewrite !expr0|].
  by rewrite exprS // exprS // inzmodM => ->.
qed.

lemma inzmod_exp (m n : int) :
  inzmod (exp m n) =
  if 0 <= n
  then exp (inzmod m) n
  else exp (inzmod m) (-n).
proof.
  move: (exp_inzmod m n); case: (0 <= n) => [_ -> //|/ltzNge ltn0].
  by rewrite !exprN => ->; rewrite invrK.
qed.

lemma inzmod_exp_mod (m n k : int) :
  inzmod (exp m k) = one =>
  inzmod (exp m n) =
  if 0 <= n
  then inzmod (exp m (n %% k))
  else inzmod (exp m ((-n) %% k)).
proof.
  case: (k = 0) => [->>|]; [by rewrite !modz0 exprN; case: (0 <= n)|].
  rewrite -normr_gt0 pow_normr -modz_abs inzmod_exp normr_ge0 /=.
  move => lt0normr eq_inzmod_one; case: (0 <= n) => [le0n|Nle0n].
  + rewrite inzmod_exp le0n /= {1}(divz_eq n `|k|) exprD_nneg.
    - by rewrite mulr_ge0; [rewrite divz_ge0|rewrite normr_ge0].
    - by rewrite modz_ge0 gtr_eqF.
    rewrite Ring.IntID.mulrC exprM eq_inzmod_one expr1z.
    by rewrite mul1r exp_inzmod modz_ge0 // gtr_eqF.
  move: Nle0n => /ltrNge; rewrite -exprN -oppr_gt0 => /ltzW le0Nn.
  rewrite inzmod_exp le0Nn /= {1}(divz_eq (-n) `|k|) exprD_nneg.
  + by rewrite mulr_ge0; [rewrite divz_ge0|rewrite normr_ge0].
  + by rewrite modz_ge0 gtr_eqF.
  rewrite Ring.IntID.mulrC exprM eq_inzmod_one expr1z.
  rewrite mul1r exp_inzmod modz_ge0 /=; [by rewrite gtr_eqF|].
  by rewrite modz_abs.
qed.

lemma exp_mod (x : zmod) n k :
  exp x k = one =>
  exp x n = exp x (n %% k).
proof.
  case: (k = 0) => [->>|neqk0]; [by rewrite modz0|].
  rewrite -(asintK x) => eq_exp_one; rewrite exp_inzmod.
  case: (0 <= n) => [le0n|Nle0n].
  + rewrite (inzmod_exp_mod (asint x) n k).
    - move: eq_exp_one; rewrite exp_inzmod.
      by case (0 <= k) => // _; rewrite exprN invr_eq1.
    by rewrite le0n /= inzmod_exp modz_ge0.
  rewrite -(invrK (exp (inzmod _) _)); apply congr1.
  rewrite -exprN -(mul1r (exp _ _)).
  rewrite -(expr1z (- n %/ k)) -eq_exp_one -exprM mulrN Ring.IntID.mulrC -exprD.
  + apply/negP => eq_inzmod_zero; move: eq_inzmod_zero eq_exp_one => ->.
    by rewrite expr0z neqk0 /= eq_sym oner_neq0.
  by rewrite -opprD -divz_eq inzmod_exp oppr_ge0 ltzW //= ltrNge.
qed.

lemma exp_sub_p_1 (x : zmod) :
  unit x =>
  exp x (p - 1) = one.
proof.
elim/inzmodW: x => x rg_x /unitE; rewrite inzmod_eq0P => N_p_div_x.
rewrite exp_inzmod ifT; first by smt(ge2_p).
by rewrite -[one]asintK oneE -eq_inzmod zmodcgrP &(Fermat_little) // prime_p.
qed.

lemma exp_p (x : zmod) :
  exp x p = x.
proof.
  case: (unit x) => [unitx|].
  + by rewrite -(Ring.IntID.subrK p 1) exprD -?unitE // expr1 exp_sub_p_1 // mul1r.
  rewrite unitE /= => ->; rewrite expr0z.
  by move: prime_p; rewrite /prime; case (p = 0) => // ->.
qed.

lemma inv_exp_sub_p_2 x :
  unit x =>
  inv x = exp x (p - 2).
proof.
  move => unitx; rewrite -div1r; move: (eqf_div one x (exp x (p - 2)) one).
  rewrite -unitE unitx oner_neq0 -div1r !mul1r divr1 /= -exprSr /=.
  + by rewrite subr_ge0 ge2_p.
  by rewrite exp_sub_p_1.
qed.

end ZModField.
