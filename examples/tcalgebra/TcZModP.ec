(* -------------------------------------------------------------------- *)
require import AllCore List Distr Int IntDiv.
require import TcMonoid TcRing TcBigop TcBigalg TcInt.
require import StdOrder.
(*---*) import IntOrder.
require (*--*) Subtype.

(* ==================================================================== *)
(* This abstract theory provides the construction of the ring [Z/pZ]    *)
(* as a TC carrier. Mirrors [theories/algebra/ZModP.ec:ZModRing], but    *)
(* the [comring]/[idomain] structure is carried by a single             *)
(* [instance comring with zmod] declaration rather than via             *)
(* [clone Ring.ComRing as ZModpRing] + a redundant [instance ring].     *)
(* ==================================================================== *)
abstract theory ZModRing.

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

lemma eq_inzmod (z1 z2 : int) : zmodcgr z1 z2 <=> inzmod z1 = inzmod z2.
proof. split.
+ by move=> h; apply/asint_inj; rewrite !inzmodK.
+ by move/(congr1 asint); rewrite !inzmodK.
qed.

lemma asint_eq (z1 z2 : zmod) : (asint z1 = asint z2) <=> (z1 = z2).
proof. by split=> [/asint_inj|->//]. qed.

(* -------------------------------------------------------------------- *)
(* The ring ops on [zmod]. Direct definitions (not via a private        *)
(* [theory ZModule]); the [instance comring with zmod] below proves the *)
(* axioms with [exact:] on these named lemmas.                          *)
(* -------------------------------------------------------------------- *)
op zmod_zero       = inzmod 0.
op zmod_one        = inzmod 1.
op zmod_opp x      = inzmod (- asint x).
op zmod_add x y    = inzmod (asint x + asint y).
op zmod_mul x y    = inzmod (asint x * asint y).

op zmod_unit x     = exists y, zmod_mul y x = zmod_one.
op zmod_inv  x     = choiceb (fun y => zmod_mul y x = zmod_one) x.

(* -------------------------------------------------------------------- *)
lemma zmod_zeroE: asint zmod_zero = 0.
proof. by rewrite /zmod_zero inzmodK mod0z. qed.

lemma zmod_oneE: asint zmod_one = 1.
proof. by rewrite /zmod_one inzmodK modz_small; smt(ge2_p). qed.

lemma zmod_oppE (x : zmod): asint (zmod_opp x) = (- (asint x)) %% p.
proof. by rewrite /zmod_opp /inzmod /asint /= Sub.insubdK; smt(ge2_p). qed.

lemma zmod_addE (x y : zmod):
  asint (zmod_add x y) = (asint x + asint y) %% p.
proof. by rewrite /zmod_add /inzmod /asint /= Sub.insubdK; smt(ge2_p). qed.

lemma zmod_mulE (x y : zmod):
  asint (zmod_mul x y) = (asint x * asint y) %% p.
proof. rewrite /zmod_mul /inzmod /asint /= Sub.insubdK; smt(ge2_p). qed.

(* -------------------------------------------------------------------- *)
(* Ring axioms on [zmod]. Proofs go through [asint_inj] + concrete int  *)
(* arithmetic; identical body to the legacy [ZModule]/[ComRing] proofs. *)
(* -------------------------------------------------------------------- *)
lemma zmod_addrA (x y z : zmod):
  zmod_add x (zmod_add y z) = zmod_add (zmod_add x y) z.
proof. by apply/asint_inj; rewrite !zmod_addE modzDml modzDmr addzA. qed.

lemma zmod_addrC (x y : zmod): zmod_add x y = zmod_add y x.
proof. by apply/asint_inj; rewrite !zmod_addE addzC. qed.

lemma zmod_add0r (x : zmod): zmod_add zmod_zero x = x.
proof.
by apply/asint_inj; rewrite !(zmod_addE, zmod_zeroE) add0z;
   smt(rg_asint pmod_small ge2_p).
qed.

lemma zmod_addrN (x : zmod): zmod_add x (zmod_opp x) = zmod_zero.
proof.
apply/asint_inj; rewrite !(zmod_zeroE, zmod_addE, zmod_oppE).
by rewrite modzDmr addzN.
qed.

lemma zmod_oner_neq0 : zmod_one <> zmod_zero.
proof. by rewrite -eq_inzmod #smt:(ge2_p). qed.

lemma zmod_mulrA (x y z : zmod):
  zmod_mul x (zmod_mul y z) = zmod_mul (zmod_mul x y) z.
proof. by apply/asint_inj; rewrite !zmod_mulE modzMml modzMmr mulzA. qed.

lemma zmod_mulrC (x y : zmod): zmod_mul x y = zmod_mul y x.
proof. by apply/asint_inj; rewrite !zmod_mulE mulzC. qed.

lemma zmod_mul1r (x : zmod): zmod_mul zmod_one x = x.
proof.
by apply/asint_inj; rewrite !(zmod_mulE, zmod_oneE) mul1z; smt(rg_asint).
qed.

lemma zmod_mulrDl (x y z : zmod):
  zmod_mul (zmod_add x y) z = zmod_add (zmod_mul x z) (zmod_mul y z).
proof.
apply/asint_inj; rewrite !(zmod_addE, zmod_mulE).
by rewrite !(modzMml, modzMmr, modzDml, modzDmr) mulzDl.
qed.

lemma zmod_mulVr x : zmod_unit x => zmod_mul (zmod_inv x) x = zmod_one.
proof. by move/choicebP=> /(_ x). qed.

lemma zmod_unitP x y : zmod_mul y x = zmod_one => zmod_unit x.
proof. by move=> eq; exists y. qed.

lemma zmod_unitout x : ! zmod_unit x => zmod_inv x = x.
proof.
move=> Nux; rewrite /zmod_inv choiceb_dfl //= => y; apply/negP.
by move=> h; apply/Nux; exists y.
qed.

(* -------------------------------------------------------------------- *)
(* [comring] is the right level: [zmod] is commutative and has the      *)
(* abstract [unit]/[inv] machinery via [choiceb], but it's not an       *)
(* [idomain] for non-prime [p] (zero divisors exist). Field instance    *)
(* lives in [ZModField] below.                                          *)
(* -------------------------------------------------------------------- *)
instance comring with zmod reducible
  op idm   = zmod_zero
  op (+)   = zmod_add
  op [-]   = zmod_opp
  op oner  = zmod_one
  op ( * ) = zmod_mul
  op invr  = zmod_inv
  op unit  = zmod_unit

  proof addmA      by exact: zmod_addrA
  proof addmC      by exact: zmod_addrC
  proof add0m      by exact: zmod_add0r
  proof addrN      by exact: zmod_addrN
  proof oner_neq0  by exact: zmod_oner_neq0
  proof mulrA      by exact: zmod_mulrA
  proof mulrC      by exact: zmod_mulrC
  proof mul1r      by exact: zmod_mul1r
  proof mulrDl     by exact: zmod_mulrDl
  proof mulVr      by exact: zmod_mulVr
  proof unitP      by exact: zmod_unitP
  proof unitout    by exact: zmod_unitout.

(* Spacer: flush deferred-proof state before downstream uses.          *)
op _spacer1 : zmod = zmod_zero.

(* ==================================================================== *)
(* inzmod/asint corollaries — these are the user-facing identities      *)
(* tying the carrier coercions to the abstract class ops.              *)
(* ==================================================================== *)
lemma inzmodD (a b : int):
  inzmod (a + b) = zmod_add (inzmod a) (inzmod b).
proof. by apply/asint_inj; rewrite zmod_addE !inzmodK modzDmr modzDml. qed.

lemma inzmodM (a b : int):
  inzmod (a * b) = zmod_mul (inzmod a) (inzmod b).
proof. by apply/asint_inj; rewrite zmod_mulE !inzmodK modzMmr modzMml. qed.

lemma inzmodN (n : int):
  inzmod (- n) = zmod_opp (inzmod n).
proof. by apply/asint_inj; rewrite zmod_oppE !inzmodK modzNm. qed.

lemma inzmodB (a b : int):
  inzmod (a - b) = zmod_add (inzmod a) (zmod_opp (inzmod b)).
proof. by rewrite inzmodD inzmodN. qed.

lemma inzmodD_mod (a b : int):
  inzmod ((a + b) %% p) = zmod_add (inzmod a) (inzmod b).
proof. by rewrite -inzmod_mod inzmodD. qed.

lemma inzmodM_mod (a b : int):
  inzmod ((a * b) %% p) = zmod_mul (inzmod a) (inzmod b).
proof. by rewrite -inzmod_mod inzmodM. qed.

lemma inzmodN_mod (n : int):
  inzmod ((- n) %% p) = zmod_opp (inzmod n).
proof. by rewrite -inzmod_mod inzmodN. qed.

lemma inzmodB_mod (a b : int):
  inzmod ((a - b) %% p) = zmod_add (inzmod a) (zmod_opp (inzmod b)).
proof. by rewrite -inzmod_mod inzmodB. qed.

(* -------------------------------------------------------------------- *)
lemma zmodcgrP (i j : int) : zmodcgr i j <=> p %| (i - j).
proof. by rewrite dvdzE -[0](mod0z p) !eq_inzmod inzmodB subr_eq0. qed.

lemma inzmod_eq0P (i : int) : inzmod i = zmod_zero <=> p %| i.
proof. by rewrite -[zmod_zero]asintK zmod_zeroE -eq_inzmod zmodcgrP. qed.

(* -------------------------------------------------------------------- *)
lemma inzmodW (P : zmod -> bool) :
  (forall i, 0 <= i < p => P (inzmod i)) => forall n, P n.
proof. by move=> ih n; rewrite -(asintK n) &(ih) rg_asint. qed.

(* ==================================================================== *)
(* Distribution / finiteness layer (verbatim from legacy ZModP).        *)
(* ==================================================================== *)
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
(* Field structure when [p] is prime. Inherits ZModRing's subtype, ops,*)
(* and comring instance via [clone include]; adds [unitE] and the      *)
(* [field] instance.                                                   *)
(* ==================================================================== *)
abstract theory ZModField.

const p : { int | prime p } as prime_p.

clone include ZModRing with
  op    p <- p
  proof ge2_p by smt(gt1_prime prime_p).

lemma unitE (x : zmod) : zmod_unit x <=> x <> zmod_zero.
proof.
split; first by apply: contraL => ->; smt(zmod_mulrC zmod_mul1r choicebP).
move=> nz_x; exists (inzmod (invm (asint x) p)).
apply: asint_inj; rewrite zmod_oneE zmod_mulE inzmodK.
rewrite (@modzE (invm _ _)) -mulNr mulrDl mulrAC modzMDr mulrC.
apply/mulmV; first by apply/prime_p.
by move: nz_x; rewrite -asint_eq zmod_zeroE pmod_small // rg_asint.
qed.

lemma zmod_mulrV (x : zmod) :
  x <> zmod_zero => zmod_mul x (zmod_inv x) = zmod_one.
proof.
move=> nz_x; rewrite zmod_mulrC; apply: zmod_mulVr; rewrite unitE //.
qed.

lemma zmod_mulf_eq0 (x y : zmod) :
  zmod_mul x y = zmod_zero <=> x = zmod_zero \/ y = zmod_zero.
proof.
split; last first.
- by case=> ->; apply/asint_inj;
    rewrite zmod_mulE zmod_zeroE; smt(zmod_zeroE rg_asint).
move/(congr1 asint); rewrite zmod_mulE zmod_zeroE => /dvdzE dvd.
have [dvd'|dvd'] : p %| asint x \/ p %| asint y by smt(prime_p).
- by left; apply/asint_inj; rewrite zmod_zeroE; smt(rg_asint dvdzE).
- by right; apply/asint_inj; rewrite zmod_zeroE; smt(rg_asint dvdzE).
qed.

(* Comring (and ancestors) inherited from ZModRing's instance via the
   clone include. Two refinements stack on top: idomain adds mulf_eq0,
   then field adds unitfP. *)
instance idomain with zmod reducible
  proof mulf_eq0 by exact: zmod_mulf_eq0.

instance field with zmod reducible
  proof unitfP by exact: unitE.

(* Spacer. *)
op _spacer2 : zmod = zmod_zero.

end ZModField.
