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
op zmod_opp x      = inzmod (- asint x).
op zmod_add x y    = inzmod (asint x + asint y).
op zmod_mul x y    = inzmod (asint x * asint y).

op zmod_unit x     = exists y, zmod_mul y x = inzmod 1.
op zmod_inv  x     = choiceb (fun y => zmod_mul y x = inzmod 1) x.

(* Carrier-specific abbrevs for [+] / [*] / [-]. Not strictly required
   anymore — the resolver's op-preservation filter (via
   [tci_chain_rename]) now disambiguates the two monoid views on
   comring carriers correctly — but kept for parity with Int.ec /
   Real.ec, faster elaboration (no TC inference), and explicit
   printer behaviour.                                                  *)
abbrev ( + ) (x y : zmod) : zmod = zmod_add x y.
abbrev ( * ) (x y : zmod) : zmod = zmod_mul x y.
abbrev [-] (x : zmod) : zmod = zmod_opp x.

(* -------------------------------------------------------------------- *)
lemma inzmod0E: asint (inzmod 0) = 0.
proof. by rewrite inzmodK mod0z. qed.

lemma inzmod1E: asint (inzmod 1) = 1.
proof. by rewrite inzmodK modz_small; smt(ge2_p). qed.

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

lemma zmod_add0r (x : zmod): zmod_add (inzmod 0) x = x.
proof.
by apply/asint_inj; rewrite !(zmod_addE, inzmod0E) add0z;
   smt(rg_asint pmod_small ge2_p).
qed.

lemma zmod_addrN (x : zmod): zmod_add x (zmod_opp x) = inzmod 0.
proof.
apply/asint_inj; rewrite !(inzmod0E, zmod_addE, zmod_oppE).
by rewrite modzDmr addzN.
qed.

lemma zmod_oner_neq0 : inzmod 1 <> inzmod 0.
proof. by rewrite -eq_inzmod #smt:(ge2_p). qed.

lemma zmod_mulrA (x y z : zmod):
  zmod_mul x (zmod_mul y z) = zmod_mul (zmod_mul x y) z.
proof. by apply/asint_inj; rewrite !zmod_mulE modzMml modzMmr mulzA. qed.

lemma zmod_mulrC (x y : zmod): zmod_mul x y = zmod_mul y x.
proof. by apply/asint_inj; rewrite !zmod_mulE mulzC. qed.

lemma zmod_mul1r (x : zmod): zmod_mul (inzmod 1) x = x.
proof.
by apply/asint_inj; rewrite !(zmod_mulE, inzmod1E) mul1z; smt(rg_asint).
qed.

lemma zmod_mulrDl (x y z : zmod):
  zmod_mul (zmod_add x y) z = zmod_add (zmod_mul x z) (zmod_mul y z).
proof.
apply/asint_inj; rewrite !(zmod_addE, zmod_mulE).
by rewrite !(modzMml, modzMmr, modzDml, modzDmr) mulzDl.
qed.

lemma zmod_mulVr x : zmod_unit x => zmod_mul (zmod_inv x) x = inzmod 1.
proof. by move/choicebP=> /(_ x). qed.

lemma zmod_unitP x y : zmod_mul y x = inzmod 1 => zmod_unit x.
proof. by move=> eq; exists y. qed.

lemma zmod_unitout x : ! zmod_unit x => zmod_inv x = x.
proof.
move=> Nux; rewrite /zmod_inv choiceb_dfl //= => y; apply/negP.
by move=> h; apply/Nux; exists y.
qed.

(* -------------------------------------------------------------------- *)
(* [comring] is the right level: [zmod] is commutative and has the      *)
(* abstract [unit]/[inv] machinery via [choiceb], but it's not an       *)
(* [idomain] for non-prime [p] (zeror divisors exist). Field instance    *)
(* lives in [ZModField] below.                                          *)
(* -------------------------------------------------------------------- *)
instance comring with zmod
  op zeror  = (inzmod 0)
  op (+)   = zmod_add
  op [-]   = zmod_opp
  op oner  = (inzmod 1)
  op ( * ) = zmod_mul
  op invr  = zmod_inv
  op unit  = zmod_unit

  proof mopA<:addmonoid>  by exact: zmod_addrA
  proof mopC<:addmonoid>  by exact: zmod_addrC
  proof mop0<:addmonoid>  by exact: zmod_add0r
  proof addrN             by exact: zmod_addrN
  proof oner_neq0         by exact: zmod_oner_neq0
  proof mopA<:mulmonoid>  by exact: zmod_mulrA
  proof mopC<:mulmonoid>  by exact: zmod_mulrC
  proof mop0<:mulmonoid>  by exact: zmod_mul1r
  proof mulrDl            by exact: zmod_mulrDl
  proof mulVr             by exact: zmod_mulVr
  proof unitP             by exact: zmod_unitP
  proof unitout           by exact: zmod_unitout.

(* Spacer: flush deferred-proof state before downstream uses.          *)
op _spacer1 : zmod = inzmod 0.

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

lemma inzmod_eq0P (i : int) : inzmod i = inzmod 0 <=> p %| i.
proof. by rewrite -[inzmod 0]asintK inzmod0E -eq_inzmod zmodcgrP. qed.

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

lemma unitE (x : zmod) : zmod_unit x <=> x <> inzmod 0.
proof.
split; first by apply: contraL => ->; apply: (unitr0<:zmod>).
move=> nz_x; exists (inzmod (invm (asint x) p)).
apply: asint_inj; rewrite inzmod1E zmod_mulE inzmodK.
rewrite (@modzE (invm _ _)) -mulNr mulrDl mulrAC modzMDr mulrC.
apply/mulmV; first by apply/prime_p.
by move: nz_x; rewrite -asint_eq inzmod0E pmod_small // rg_asint.
qed.

lemma zmod_mulrV (x : zmod) :
  x <> inzmod 0 => zmod_mul x (zmod_inv x) = inzmod 1.
proof.
move=> nz_x; rewrite zmod_mulrC; apply: zmod_mulVr; rewrite unitE //.
qed.

lemma zmod_mulf_eq0 (x y : zmod) :
  zmod_mul x y = inzmod 0 <=> x = inzmod 0 \/ y = inzmod 0.
proof.
case: (x = inzmod 0) => //= [->|]; first by rewrite mul0r.
move=> nz_x; split=> [|->]; last by rewrite mulr0.
move=> h; apply: (mulrI x); last by rewrite mulr0.
by rewrite unitE.
qed.

(* Comring (and ancestors) inherited from ZModRing's instance via the
   clone include. Two refinements stack on top: idomain adds mulf_eq0,
   then field adds unitfP. *)
instance idomain with zmod
  proof mulf_eq0 by exact: zmod_mulf_eq0.

instance field with zmod
  proof unitfP by exact: unitE.

(* Spacer. *)
op _spacer2 : zmod = inzmod 0.

(* ==================================================================== *)
(* Field-specific exp/Fermat corollaries. Mirrors the tail of legacy   *)
(* ZModField (lines 372–467 of theories/algebra/ZModP.ec).             *)
(*                                                                     *)
(* The class-op [exp] is comring's; for nonzero (i.e. [unit]) [x : zmod],
   it behaves like [int]'s [exp] modulo [p].                           *)
(* ==================================================================== *)

(* [exp_mod] specialised to [zmod]: when [x] has order dividing [k], the
   exponent only matters mod [k]. The [unit x] precondition from the
   general comring lemma is automatic over a field except at [x = 0],
   handled separately below. *)
lemma exp_mod (x : zmod) (n k : int) :
  x <> inzmod 0 => exp x k = inzmod 1 =>
  exp x n = exp x (n %% k).
proof.
by move=> nz_x; apply: exp_mod_unit; apply/unitE.
qed.

(* Fermat's little theorem: every unit raised to [p - 1] is one.       *)
lemma exp_sub_p_1 (x : zmod) :
  unit x => exp x (p - 1) = inzmod 1.
proof.
move=> ux.
have nz_x: x <> inzmod 0 by apply/unitE.
have N_p_div_x: !(p %| asint x).
+ rewrite -inzmod_eq0P; move: nz_x.
  by rewrite -{1}(@asintK x).
have ge0_p1: 0 <= p - 1 by smt(prime_p gt1_prime).
have lift_exp : forall i, 0 <= i =>
  exp (inzmod (asint x)) i = inzmod (exp<:int> (asint x) i).
+ elim=> [|i ge0_i ih]; first by rewrite !expr0.
  by rewrite !exprS // ih inzmodM asintK.
rewrite -{1}(@asintK x) lift_exp //.
rewrite -[inzmod 1]asintK inzmod1E -eq_inzmod.
by rewrite zmodcgrP &(Fermat_little) // prime_p.
qed.

(* Fermat consequence: [x ^ p = x] for any [x : zmod] (including 0).   *)
lemma exp_p (x : zmod) : exp x p = x.
proof.
case: (unit x) => [ux|].
+ by rewrite -(subrK p 1) exprD // expr1 exp_sub_p_1 // mul1r.
rewrite unitE /= => ->; rewrite expr0z.
by move: prime_p; rewrite /prime; case (p = 0) => // ->.
qed.

(* Inverse via Fermat: [invr x = x ^ (p - 2)] when [x] is a unit.      *)
lemma inv_exp_sub_p_2 (x : zmod) :
  unit x => invr x = exp x (p - 2).
proof.
move=> ux; rewrite -div1r; move: (eqf_div oner x (exp x (p - 2)) oner).
rewrite -unitE ux oner_neq0 -div1r !mul1r divr1 /= -exprSr /=.
+ by smt(prime_p gt1_prime).
by rewrite exp_sub_p_1.
qed.

end ZModField.
