(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
require import AllCore.
require (*--*) Ring StdRing.

pragma +implicits.
pragma -oldip.

(* -------------------------------------------------------------------- *)
pred homo2 ['a 'b] (op_ : 'a -> 'b) (aR : 'a rel) (rR : 'b rel) =
  forall x y, aR x y => rR (op_ x) (op_ y).

pred mono2 ['a 'b] (op_ : 'a -> 'b) (aR : 'a rel) (rR : 'b rel) =
  forall x y, rR (op_ x) (op_ y) <=> aR x y.

lemma mono2W f (aR : 'a rel) (rR : 'b rel) :
  mono2 f aR rR => homo2 f aR rR.
proof. by move=> + x y - ->. qed.

lemma monoLR ['a 'b] f g (aR : 'a rel) (rR : 'b rel) :
  cancel g f => mono2 f aR rR => forall x y,
    rR (f x) y <=> aR x (g y).
proof. by move=> can_gf mf x y; rewrite -{1}can_gf mf. qed.

lemma monoRL ['a 'b] f g (aR : 'a rel) (rR : 'b rel) :
  cancel g f => mono2 f aR rR => forall x y,
    rR x (f y) <=> aR (g x) y.
proof. by move=> can_gf mf x y; rewrite -{1}can_gf mf. qed.

(* -------------------------------------------------------------------- *)
abstract theory RealDomain.
type t.

clone import Ring.IDomain as Domain with type t <- t.

op "`|_|" : t -> t.
op ( <= ) : t -> t -> bool.
op ( <  ) : t -> t -> bool.

op minr : t -> t -> t.
op maxr : t -> t -> t.

theory Axioms.
  axiom nosmt ler_norm_add (x y : t): `|x + y| <= `|x| + `|y|.
  axiom nosmt addr_gt0     (x y : t): zeror < x => zeror < y => zeror < (x + y).
  axiom nosmt norm_eq0     (x   : t): `|x| = zeror => x = zeror.
  axiom nosmt ger_leVge    (x y : t): zeror <= x => zeror <= y => (x <= y) \/ (y <= x).
  axiom nosmt normrM       (x y : t): `|x * y| = `|x| * `|y|.
  axiom nosmt ler_def      (x y : t): x <= y <=> `|y - x| = y - x.
  axiom nosmt ltr_def      (x y : t): x < y <=> (y <> x) /\ x <= y.
  axiom nosmt real_axiom   (x   : t): zeror <= x \/ x <= zeror.
  axiom nosmt minrE        (x y : t): minr x y = if x <= y then x else y.
  axiom nosmt maxrE        (x y : t): maxr x y = if y <= x then x else y.
end Axioms.

clear [Axioms.*].

lemma nosmt ler_norm_add (x y : t): `|x + y| <= `|x| + `|y|.
proof. by apply/Axioms.ler_norm_add. qed.

lemma nosmt addr_gt0 (x y : t): zeror < x => zeror < y => zeror < x + y.
proof. by apply/Axioms.addr_gt0. qed.

lemma nosmt normr0_eq0 (x : t): `|x| = zeror => x = zeror.
proof. by apply/Axioms.norm_eq0. qed.

lemma nosmt ger_leVge (x y : t):
  zeror <= x => zeror <= y => (x <= y) \/ (y <= x).
proof. by apply/Axioms.ger_leVge. qed.

lemma nosmt normrM (x y : t): `|x * y| = `|x| * `|y|.
proof. by apply/Axioms.normrM. qed.

lemma nosmt ler_def (x y : t): (x <= y) <=> (`|y - x| = y - x).
proof. by apply/Axioms.ler_def. qed.

lemma nosmt ltr_def (x y : t): (x < y) <=> (y <> x) /\ (x <= y).
proof. by apply/Axioms.ltr_def. qed.

lemma real_axiom (x : t): (zeror <= x) \/ (x <= zeror).
proof. by apply/Axioms.real_axiom. qed.

lemma minrE (x y : t): minr x y = if x <= y then x else y.
proof. by apply/Axioms.minrE. qed.

lemma maxrE (x y : t): maxr x y = if y <= x then x else y.
proof. by apply/Axioms.maxrE. qed.

lemma ger0_def (x : t): (zeror <= x) <=> (`|x| = x).
proof. by rewrite ler_def subr0. qed.

lemma subr_ge0 (x y : t): (zeror <= x - y) <=> (y <= x).
proof. by rewrite ger0_def -ler_def. qed.

lemma oppr_ge0 (x : t): (zeror <= -x) <=> (x <= zeror).
proof. by rewrite -sub0r subr_ge0. qed.

lemma ler01: zeror <= oner.
proof.
have n1_nz: `|oner| <> zeror by apply/(contraNneq _ _ oner_neq0) => /normr0_eq0->.
by rewrite ger0_def -(inj_eq (mulfI _ n1_nz)) -normrM !mulr1.
qed.

lemma ltr01: zeror < oner.
proof. by rewrite ltr_def oner_neq0 ler01. qed.

hint exact : ler01 ltr01.

lemma ltrW (x y : t): x < y => x <= y.
proof. by rewrite ltr_def. qed.

lemma nosmt lerr (x : t): x <= x.
proof.
have n2: `|ofint 2| = (ofint 2).
  rewrite -ger0_def (@ofintS 1) // ofint1 ltrW //.
  by rewrite addr_gt0 ?ltr01.
rewrite ler_def subrr -(inj_eq (addrI `|zeror|)) /= addr0.
by rewrite -mulr2z -mulr_intr -n2 -normrM mul0r.
qed.

hint exact : lerr.

lemma nosmt lerr_eq (x y : t): x = y => x <= y.
proof. by move=> ->; rewrite lerr. qed.

lemma nosmt ltrr (x : t): !(x < x).
proof. by rewrite ltr_def. qed.

lemma nosmt ltr_neqAle (x y : t):
  (x < y) <=> (x <> y) /\ (x <= y).
proof. by rewrite ltr_def eq_sym. qed.

lemma nosmt ler_eqVlt (x y : t):
  (x <= y) <=> (x = y) \/ (x < y).
proof. by rewrite ltr_neqAle; case: (x = y)=> // ->; rewrite lerr. qed.

lemma nosmt lt0r (x : t):
  (zeror < x) <=> (x <> zeror) /\ (zeror <= x).
proof. by rewrite ltr_def. qed.

lemma nosmt le0r (x : t):
  (zeror <= x) <=> (x = zeror) \/ (zeror < x).
proof. by rewrite ler_eqVlt eq_sym. qed.

lemma nosmt addr_ge0 (x y : t):
  zeror <= x => zeror <= y => zeror <= x + y.
proof.
rewrite le0r; case=> [->|gt0x]; rewrite ?add0r // le0r.
by case=> [->|gt0y]; rewrite ltrW ?addr0 ?addr_gt0.
qed.

lemma nosmt lt0r_neq0 (x : t):
  zeror < x => (x <> zeror).
proof. by rewrite lt0r; case (_ = _). qed.

lemma nosmt ltr0_neq0 (x : t):
  zeror < x => (x <> zeror).
proof. by rewrite lt0r; case: (_ = _). qed.

lemma nosmt gtr_eqF (x y : t):
  y < x => (x <> y).
proof. by rewrite ltr_def => -[]. qed.

lemma nosmt ltr_eqF (x y : t):
  x < y => (x <> y).
proof. by rewrite eq_sym=> /gtr_eqF ->. qed.

lemma ler0n n : 0 <= n => zeror <= ofint n.
proof.
elim: n => [|n ih h]; first by rewrite ofint0 lerr.
by rewrite ofintS // addr_ge0 // ?ler01.
qed.

lemma ltr0Sn n : 0 <= n => zeror < ofint (n + 1).
proof.
elim: n=> /= [|n ge0n ih]; first by rewrite ofint1 ltr01.
by rewrite (@ofintS (n+1)) // ?(addz_ge0, addr_gt0) // ltr01.
qed.

lemma ltr0n n : 0 <= n => (zeror < ofint n) = (0 < n).
proof.
elim: n => [|n ge0n _]; first by rewrite ofint0 ltrr.
by rewrite ltr0Sn // ltz_def addz_ge0 ?addz1_neq0.
qed.

lemma pnatr_eq0 n : 0 <= n => (ofint n = zeror) <=> (n = 0).
proof.
elim: n => [|n ge0n _]; rewrite ?ofint0 // gtr_eqF.
  by apply: ltr0Sn. by rewrite addz1_neq0.
qed.

lemma nosmt pmulr_rgt0 (x y : t):
  zeror < x => (zeror < x * y) <=> (zeror < y).
proof.
rewrite !ltr_def !ger0_def normrM mulf_eq0 negb_or.
by case=> ^nz_x -> -> /=; have /inj_eq -> := mulfI _ nz_x.
qed.

lemma nosmt pmulr_rge0 (x y : t):
  zeror < x => (zeror <= x * y) <=> (zeror <= y).
proof.
rewrite !le0r mulf_eq0; case: (y = _) => //= ^lt0x.
by move/lt0r_neq0=> -> /=; apply/pmulr_rgt0.
qed.

lemma nosmt normr_idP (x : t): (`|x| = x) <=> (zeror <= x).
proof. by rewrite ger0_def. qed.

lemma nosmt ger0_norm (x : t): zeror <= x => `|x| = x.
proof. by apply/normr_idP. qed.

lemma nosmt normr0: `|zeror| = zeror.
proof. by apply/ger0_norm/lerr. qed.

lemma nosmt normr1: `|oner| = oner.
proof. by apply/ger0_norm/ler01. qed.

lemma nosmt normr_nat n : 0 <= n => `|ofint n| = ofint n.
proof. by move=> n_0ge; rewrite ger0_norm // ler0n. qed.

lemma nosmt normr0P (x : t): (`|x| = zeror) <=> (x = zeror).
proof. by split=> [/normr0_eq0|->] //; rewrite normr0. qed.

lemma nosmt normr_unit : forall x, unit x => unit `|x|.
proof.
move=> x /unitrP [y yx]; apply/unitrP; exists `|y|.
by rewrite -normrM yx normr1.
qed.

lemma nosmt normrV : forall x, unit x => `|invr x| = invr `|x|.
proof.
move=>x ux; apply/(@mulrI `|x|); first by apply/normr_unit.
by rewrite -normrM !mulrV ?normr_unit // normr1.
qed.

lemma nosmt normrX_nat n (x : t) : 0 <= n => `|exp x n| = exp `|x| n.
proof.
elim: n=> [|n ge0_n ih]; first by rewrite !expr0 normr1.
by rewrite !exprS //= normrM ih.
qed.

lemma nosmt normrN1: `|-oner| = oner.
proof.
have: exp `|-oner| 2 = oner.
  by rewrite -normrX_nat -1?signr_odd // odd2 expr0 normr1.
rewrite sqrf_eq1=> -[->//|]; rewrite -ger0_def le0r oppr_eq0.
by rewrite oner_neq0 /= => /(addr_gt0 _ _ ltr01); rewrite addrN ltrr.
qed.

lemma nosmt normrN (x : t): `|- x| = `|x|.
proof. by rewrite -mulN1r normrM normrN1 mul1r. qed.

lemma nosmt distrC (x y : t): `|x - y| = `|y - x|.
proof. by rewrite -opprB normrN. qed.

lemma nosmt ler0_def (x : t): (x <= zeror) <=> (`|x| = - x).
proof. by rewrite ler_def sub0r normrN. qed.

lemma nosmt normr_id (x : t): `| `|x| | = `|x|.
proof.
have nz2: ofint 2 <> zeror by rewrite pnatr_eq0.
apply: (mulfI _ nz2); rewrite -{1}normr_nat // -normrM.
rewrite mulr_intl mulr2z ger0_norm // -{2}normrN.
by rewrite -normr0 -(@subrr x) ler_norm_add.
qed.

lemma nosmt normr_ge0 (x : t): zeror <= `|x|.
proof. by rewrite ger0_def normr_id. qed.

lemma nosmt ler0_norm (x : t): x <= zeror => `|x| = - x.
proof.
move=> x_le0; rewrite eq_sym -(@ger0_norm (-x)).
  by rewrite oppr_ge0. by rewrite normrN.
qed.

lemma nosmt gtr0_norm (x : t): zeror < x => `|x| = x.
proof. by move/ltrW/ger0_norm. qed.

lemma nosmt ltr0_norm (x : t): x < zeror => `|x| = - x.
proof. by move/ltrW/ler0_norm. qed.

lemma nosmt subr_gt0 (x y : t): (zeror < y - x) <=> (x < y).
proof. by rewrite !ltr_def subr_eq0 subr_ge0. qed.

lemma nosmt subr_le0 (x y : t): (y - x <= zeror) <=> (y <= x).
proof. by rewrite -subr_ge0 opprB add0r subr_ge0. qed.

lemma nosmt subr_lt0 (x y : t): (y - x < zeror) <=> (y < x).
proof. by rewrite -subr_gt0 opprB add0r subr_gt0. qed.

lemma nosmt ler_asym (x y : t): x <= y <= x => x = y.
proof.
rewrite !ler_def distrC -opprB -addr_eq0 => -[->].
by rewrite -mulr2z -mulr_intl mulf_eq0 subr_eq0 pnatr_eq0.
qed.

lemma nosmt eqr_le (x y : t): (x = y) <=> (x <= y <= x).
proof. by split=> [->|/ler_asym]; rewrite ?lerr. qed.

lemma nosmt ltr_trans (y x z : t): x < y => y < z => x < z.
proof.
move=> le_xy le_yz; rewrite -subr_gt0 -(@subrK z y).
by rewrite -addrA addr_gt0 ?subr_gt0.
qed.

lemma nosmt ler_lt_trans (y x z : t): x <= y => y < z => x < z.
proof. by rewrite !ler_eqVlt => -[-> //|/ltr_trans h]; apply/h. qed.

lemma nosmt ltr_le_trans (y x z : t): x < y => y <= z => x < z.
proof. by rewrite !ler_eqVlt => lxy [<- //|lyz]; apply (@ltr_trans y). qed.

lemma nosmt ler_trans (y x z : t): x <= y => y <= z => x <= z.
proof.
rewrite !ler_eqVlt => -[-> //|lxy] [<-|].
  by rewrite lxy. by move/(ltr_trans _ _ _ lxy) => ->.
qed.

lemma nosmt ltr_asym (x y : t): ! (x < y < x).
proof. by apply/negP=> -[/ltr_trans hyx /hyx]; rewrite ltrr. qed.

lemma ler_anti (x y : t): x <= y <= x => x = y.
proof. by rewrite -eqr_le. qed.

lemma nosmt ltr_le_asym (x y : t): ! (x < y <= x).
proof.
rewrite andaE ltr_neqAle -andbA -!andaE.
by rewrite -eqr_le eq_sym; case: (_ = _).
qed.

lemma nosmt ler_lt_asym (x y : t):
  ! (x <= y < x).
proof. by rewrite andaE andbC -andaE ltr_le_asym. qed.

lemma nosmt ltr_geF (x y : t): x < y => ! (y <= x).
proof. by move=> xy; apply/negP => /(ltr_le_trans _ _ _ xy); rewrite ltrr. qed.

lemma nosmt ler_gtF (x y : t): x <= y => ! (y < x).
proof. by move=> le_xy; apply/negP=> /ltr_geF. qed.

lemma nosmt ltr_gtF (x y : t): x < y => ! (y < x).
proof. by move/ltrW/ler_gtF. qed.

lemma nosmt normr_le0 (x : t): (`|x| <= zeror) <=> (x = zeror).
proof. by rewrite -normr0P eqr_le normr_ge0. qed.

lemma nosmt normr_lt0 (x : t): ! (`|x| < zeror).
proof. by rewrite ltr_neqAle normr_le0 normr0P; case: (_ = _). qed.

lemma nosmt normr_gt0 (x : t): (zeror < `|x|) <=> (x <> zeror).
proof. by rewrite ltr_def normr0P normr_ge0; case: (_ = _). qed.

(*-------------------------------------------------------------------- *)
hint rewrite normrE : normr_id normr0 normr1 normrN1.
hint rewrite normrE : normr_ge0 normr_lt0 normr_le0 normr_gt0.
hint rewrite normrE : normrN.

(* -------------------------------------------------------------------- *)
lemma nosmt mono_inj f : mono2 f (<=) (<=) => injective f.
proof. by move=> mf x y; rewrite eqr_le !mf -eqr_le. qed.

lemma nosmt nmono_inj f : mono2 f (fun y x => x <= y) (<=) => injective f.
proof. by move=> mf x y; rewrite eqr_le !mf -eqr_le. qed.

lemma nosmt lerW_mono f : mono2 f (<=) (<=) => mono2 f (<) (<).
proof.
move=> mf x y; rewrite !ltr_neqAle mf.
by rewrite inj_eq //; apply/mono_inj.
qed.

lemma nosmt lerW_nmono f :
     mono2 f (fun y x => x <= y) (<=)
  => mono2 f (fun y x => x < y) (<).
proof.
move=> mf x y; rewrite !ltr_neqAle mf eq_sym.
by rewrite inj_eq //; apply/nmono_inj.
qed.

(* -------------------------------------------------------------------- *)
lemma nosmt ler_opp2 (x y : t): (-x <= -y) <=> (y <= x).
proof. by rewrite -subr_ge0 opprK addrC subr_ge0. qed.

lemma nosmt ltr_opp2 (x y : t): (-x < -y) <=> (y < x).
proof. by rewrite lerW_nmono //; apply/ler_opp2. qed.

lemma nosmt ler_oppr (x y : t): (x <= - y) <=> (y <= - x).
proof. by rewrite (monoRL opprK ler_opp2). qed.

hint rewrite lter_opp2 : ler_opp2 ltr_opp2.

lemma nosmt ltr_oppr (x y : t): (x < - y) <=> (y < - x).
proof. by rewrite (monoRL opprK (:@lerW_nmono _ ler_opp2)). qed.

lemma nosmt ler_oppl (x y : t):
  (- x <= y) <=> (- y <= x).
proof. by rewrite (monoLR opprK ler_opp2). qed.

lemma nosmt ltr_oppl (x y : t):
  (- x < y) <=> (- y < x).
proof. by rewrite (monoLR opprK (:@lerW_nmono _ ler_opp2)). qed.

lemma nosmt oppr_gt0 (x : t): (zeror < - x) <=> (x < zeror).
proof. by rewrite ltr_oppr oppr0. qed.

lemma nosmt oppr_le0 (x : t): (- x <= zeror) <=> (zeror <= x).
proof. by rewrite ler_oppl oppr0. qed.

lemma nosmt oppr_lt0 (x : t): (- x < zeror) <=> (zeror < x).
proof. by rewrite ltr_oppl oppr0. qed.

hint rewrite oppr_gte0 : oppr_ge0 oppr_gt0.
hint rewrite oppr_lte0 : oppr_le0 oppr_lt0.
hint rewrite oppr_cp0  : oppr_ge0 oppr_gt0 oppr_le0 oppr_lt0.
hint rewrite lter_oppE : oppr_le0 oppr_lt0 oppr_ge0 oppr_gt0.
hint rewrite lter_oppE : ler_opp2 ltr_opp2.

(* -------------------------------------------------------------------- *)
lemma nosmt ler_leVge (x y : t):
  x <= zeror => y <= zeror => (x <= y) \/ (y <= x).
proof. by rewrite -!oppr_ge0 => /(ger_leVge _) h /h; rewrite !ler_opp2 orbC. qed.

lemma ler_add2l (x y z : t) : (x + y <= x + z) <=> (y <= z).
proof. by rewrite -subr_ge0 opprD addrAC addNKr addrC subr_ge0. qed.

lemma ler_add2r (x y z : t) : (y + x <= z + x) <=> (y <= z).
proof. by rewrite !(@addrC _ x) ler_add2l. qed.

lemma nosmt ltr_add2r (z x y : t): (x + z < y + z) <=> (x < y).
proof. by apply/(@lerW_mono (fun t => t + z) (:@ler_add2r z)). qed.

lemma nosmt ltr_add2l (z x y : t): (z + x < z + y) <=> (x < y).
proof. by apply/(@lerW_mono (fun t => z + t) (:@ler_add2l z)). qed.

hint rewrite ler_add2  : ler_add2l ler_add2r.
hint rewrite ltr_add2  : ltr_add2l ltr_add2r.
hint rewrite lter_add2 : ler_add2l ler_add2r ltr_add2l ltr_add2r.

lemma nosmt ler_add (x y z t : t):
  x <= y => z <= t => x + z <= y + t.
proof. by move=> xy zt; rewrite (@ler_trans (y + z)) ?lter_add2. qed.

lemma nosmt ler_lt_add (x y z t : t):
  x <= y => z < t => x + z < y + t.
proof. by move=> xy zt; rewrite (@ler_lt_trans (y + z)) ?lter_add2. qed.

lemma nosmt ltr_le_add (x y z t : t):
  x < y => z <= t => x + z < y + t.
proof. by move=> xy zt; rewrite (@ltr_le_trans (y + z)) ?lter_add2. qed.

lemma nosmt ltr_add (x y z t : t): x < y => z < t => x + z < y + t.
proof. by move=> xy zt; rewrite ltr_le_add // ltrW. qed.

lemma nosmt ler_sub (x y z t : t):
  x <= y => t <= z => x - z <= y - t.
proof. by move=> xy tz; rewrite ler_add ?lter_opp2. qed.

lemma nosmt ler_lt_sub (x y z t : t):
  x <= y => t < z => x - z < y - t.
proof. by move=> xy zt; rewrite ler_lt_add ?lter_opp2. qed.

lemma nosmt ltr_le_sub (x y z t : t):
  x < y => t <= z => x - z < y - t.
proof. by move=> xy zt; rewrite ltr_le_add ?lter_opp2. qed.

lemma nosmt ltr_sub (x y z t : t):
  x < y => t < z => x - z < y - t.
proof. by move=> xy tz; rewrite ltr_add ?lter_opp2. qed.

lemma nosmt ler_subl_addr (x y z : t):
  (x - y <= z) <=> (x <= z + y).
proof. by rewrite (monoLR (:@addrK y) (:@ler_add2r (-y))). qed.

lemma nosmt ltr_subl_addr (x y z : t):
  (x - y < z) <=> (x < z + y).
proof. by rewrite (monoLR (:@addrK y) (:@ltr_add2r (-y))). qed.

lemma nosmt ler_subr_addr (x y z : t):
  (x <= y - z) <=> (x + z <= y).
proof. by rewrite (monoLR (:@addrNK z) (:@ler_add2r z)). qed.

lemma nosmt ltr_subr_addr (x y z : t):
  (x < y - z) <=> (x + z < y).
proof. by rewrite (monoLR (:@addrNK z) (:@ltr_add2r z)). qed.

hint rewrite ler_sub_addr  : ler_subl_addr ler_subr_addr.
hint rewrite ltr_sub_addr  : ltr_subl_addr ltr_subr_addr.
hint rewrite lter_sub_addr : ler_subl_addr ler_subr_addr.
hint rewrite lter_sub_addr : ltr_subl_addr ltr_subr_addr.

lemma nosmt ler_subl_addl (x y z : t):
  (x - y <= z) <=> (x <= y + z).
proof. by rewrite lter_sub_addr addrC. qed.

lemma nosmt ltr_subl_addl (x y z : t):
  (x - y < z) <=> (x < y + z).
proof. by rewrite lter_sub_addr addrC. qed.

lemma nosmt ler_subr_addl (x y z : t):
  (x <= y - z) <=> (z + x <= y).
proof. by rewrite lter_sub_addr addrC. qed.

lemma nosmt ltr_subr_addl (x y z : t):
  (x < y - z) <=> (z + x < y).
proof. by rewrite lter_sub_addr addrC. qed.

hint rewrite ler_sub_addl  : ler_subl_addl ler_subr_addl.
hint rewrite ltr_sub_addl  : ltr_subl_addl ltr_subr_addl.
hint rewrite lter_sub_addl : ler_subl_addl ler_subr_addl.
hint rewrite lter_sub_addl : ltr_subl_addl ltr_subr_addl.

lemma nosmt ler_addl (x y : t): (x <= x + y) <=> (zeror <= y).
proof. by rewrite -{1}(@addr0 x) lter_add2. qed.

lemma nosmt ltr_addl (x y : t): (x < x + y) <=> (zeror < y).
proof. by rewrite -{1}(@addr0 x) lter_add2. qed.

lemma nosmt ler_addr (x y : t): (x <= y + x) <=> (zeror <= y).
proof. by rewrite -{1}(@add0r x) lter_add2. qed.

lemma nosmt ltr_addr (x y : t): (x < y + x) <=> (zeror < y).
proof. by rewrite -{1}(@add0r x) lter_add2. qed.

lemma nosmt ger_addl (x y : t): (x + y <= x) <=> (y <= zeror).
proof. by rewrite -{2}(@addr0 x) lter_add2. qed.

lemma nosmt gtr_addl (x y : t): (x + y < x) <=> (y < zeror).
proof. by rewrite -{2}(@addr0 x) lter_add2. qed.

lemma nosmt ger_addr (x y : t): (y + x <= x) <=> (y <= zeror).
proof. by rewrite -{2}(@add0r x) lter_add2. qed.

lemma nosmt gtr_addr (x y : t): (y + x < x) <=> (y < zeror).
proof. by rewrite -{2}(@add0r x) lter_add2. qed.

hint rewrite cpr_add : ler_addl ler_addr ger_addl ger_addl.
hint rewrite cpr_add : ltr_addl ltr_addr gtr_addl gtr_addl.

lemma nosmt ler_paddl (y x z : t):
  zeror <= x => y <= z => y <= x + z.
proof. by move=> ??; rewrite -(@add0r y) ler_add. qed.

lemma nosmt ltr_paddl (y x z : t):
  zeror <= x => y < z => y < x + z.
proof. by move=> ??; rewrite -(@add0r y) ler_lt_add. qed.

lemma nosmt ltr_spaddl (y x z : t):
  zeror < x => y <= z => y < x + z.
proof. by move=> ??; rewrite -(@add0r y) ltr_le_add. qed.

lemma nosmt ltr_spsaddl (y x z : t):
  zeror < x => y < z => y < x + z.
proof. by move=> ??; rewrite -(@add0r y) ltr_add. qed.

lemma nosmt ler_naddl (y x z : t):
  x <= zeror => y <= z => x + y <= z.
proof. by move=> ??; rewrite -(@add0r z) ler_add. qed.

lemma nosmt ltr_naddl (y x z : t):
  x <= zeror => y < z => x + y < z.
proof. by move=> ??; rewrite -(@add0r z) ler_lt_add. qed.

lemma nosmt ltr_snaddl (y x z : t):
  x < zeror => y <= z => x + y < z.
proof. by move=> ??; rewrite -(@add0r z) ltr_le_add. qed.

lemma nosmt ltr_snsaddl (y x z : t):
  x < zeror => y < z => x + y < z.
proof. by move=> ??; rewrite -(@add0r z) ltr_add. qed.

lemma nosmt ler_paddr (y x z : t):
  zeror <= x => y <= z => y <= z + x.
proof. by move=> ??; rewrite (@addrC _ x) ler_paddl. qed.

lemma nosmt ltr_paddr (y x z : t):
  zeror <= x => y < z => y < z + x.
proof. by move=> ??; rewrite (@addrC _ x) ltr_paddl. qed.

lemma nosmt ltr_spaddr (y x z : t):
  zeror < x => y <= z => y < z + x.
proof. by move=> ??; rewrite (@addrC _ x) ltr_spaddl. qed.

lemma nosmt ltr_spsaddr (y x z : t):
  zeror < x => y < z => y < z + x.
proof. by move=> ??; rewrite (@addrC _ x) ltr_spsaddl. qed.

lemma nosmt ler_naddr (y x z : t):
  x <= zeror => y <= z => y + x <= z.
proof. by move=> ??; rewrite (@addrC _ x) ler_naddl. qed.

lemma nosmt ltr_naddr (y x z : t):
  x <= zeror => y < z => y + x < z.
proof. by move=> ??; rewrite (@addrC _ x) ltr_naddl. qed.

lemma nosmt ltr_snaddr (y x z : t):
  x < zeror => y <= z => y + x < z.
proof. by move=> ??; rewrite (@addrC _ x) ltr_snaddl. qed.

lemma nosmt ltr_snsaddr (y x z : t):
  x < zeror => y < z => y + x < z.
proof. by move=> ??; rewrite (@addrC _ x) ltr_snsaddl. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt paddr_eq0 (x y : t):
  zeror <= x => zeror <= y => (x + y = zeror) <=> (x = zeror) /\ (y = zeror).
proof.
rewrite le0r=> -[->|hx]; first by rewrite add0r.
by rewrite (gtr_eqF hx) /= => hy; rewrite gtr_eqF // ltr_spaddl.
qed.

lemma nosmt naddr_eq0 (x y : t):
  x <= zeror => y <= zeror => (x + y = zeror) <=> (x = zeror) /\ (y = zeror).
proof.
by move=> lex0 ley0; rewrite -oppr_eq0 opprD paddr_eq0 ?oppr_cp0 // !oppr_eq0.
qed.

lemma nosmt addr_ss_eq0 (x y : t):
  (zeror <= x) /\ (zeror <= y) \/
  (x <= zeror) /\ (y <= zeror) =>
  (x + y = zeror) <=> (x = zeror) /\ (y = zeror).
proof. by case=> -[]; [apply: paddr_eq0 | apply: naddr_eq0]. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt ler_pmul2l x :
  zeror < x => forall y z, (x * y <= x * z) <=> (y <= z).
proof.
move=> x_gt0 y z /=; rewrite -subr_ge0 -mulrBr.
by rewrite pmulr_rge0 // subr_ge0.
qed.

lemma nosmt ltr_pmul2l x :
  zeror < x => forall y z, (x * y < x * z) <=> (y < z).
proof. by move=> x_gt0; apply/lerW_mono/ler_pmul2l. qed.

hint rewrite lter_pmul2l : ler_pmul2l ltr_pmul2l.

lemma nosmt ler_pmul2r x :
  zeror < x => forall y z, (y * x <= z * x) <=> (y <= z).
proof. by move=> x_gt0 y z /=; rewrite !(@mulrC _ x) ler_pmul2l. qed.

lemma nosmt ltr_pmul2r x :
  zeror < x => forall y z, (y * x < z * x) <=> (y < z).
proof. by move=> x_gt0; apply/lerW_mono/ler_pmul2r. qed.

hint rewrite lter_pmul2r : ler_pmul2r ltr_pmul2r.

lemma nosmt ler_nmul2l x :
  x < zeror => forall y z, (x * y <= x * z) <=> (z <= y).
proof. by move=> x_lt0 y z /=; rewrite -ler_opp2 -!mulNr ler_pmul2l ?oppr_gt0. qed.

lemma nosmt ltr_nmul2l x :
  x < zeror => forall y z, (x * y < x * z) <=> (z < y).
proof. by move=> x_lt0; apply/lerW_nmono/ler_nmul2l. qed.

hint rewrite lter_nmul2l : ler_nmul2l ltr_nmul2l.

lemma nosmt ler_nmul2r x :
  x < zeror => forall y z, (y * x <= z * x) <=> (z <= y).
proof. by move=> x_lt0 y z /=; rewrite !(@mulrC _ x) ler_nmul2l. qed.

lemma nosmt ltr_nmul2r x :
  x < zeror => forall y z, (y * x < z * x) <=> (z < y).
proof. by move=> x_lt0; apply/lerW_nmono/ler_nmul2r. qed.

hint rewrite lter_nmul2r : ler_nmul2r ltr_nmul2r.

(* -------------------------------------------------------------------- *)
lemma nosmt ler_wpmul2l x :
  zeror <= x => forall y z, y <= z => x * y <= x * z.
proof.
rewrite le0r => -[-> y z|/ler_pmul2l/mono2W ? //].
  by rewrite !mul0r lerr.
qed.

lemma nosmt ler_wpmul2r x :
  zeror <= x => forall y z, y <= z => y * x <= z * x.
proof. by move=> x_ge0 y z leyz; rewrite !(@mulrC _ x) ler_wpmul2l. qed.

lemma nosmt ler_wnmul2l x :
  x <= zeror => forall y z, y <= z => x * z <= x * y.
proof.
by move=> x_le0 y z leyz; rewrite -!(@mulrNN x) ler_wpmul2l ?lter_oppE.
qed.

lemma nosmt ler_wnmul2r x :
  x <= zeror => forall y z, y <= z => z * x <= y * x.
proof.
by move=> x_le0 y z leyz; rewrite -!(@mulrNN _ x) ler_wpmul2r ?lter_oppE.
qed.

(* -------------------------------------------------------------------- *)
lemma nosmt ler_pmul (x1 y1 x2 y2 : t):
  zeror <= x1 => zeror <= x2 => x1 <= y1 => x2 <= y2 => x1 * x2 <= y1 * y2.
proof.                          (* FIXME *)
move=> x1ge0 x2ge0 le_xy1 le_xy2; have y1ge0 := ler_trans _ _ _ x1ge0 le_xy1.
have le1 := ler_wpmul2r _ x2ge0 _ _ le_xy1.
have le2 := ler_wpmul2l _ y1ge0 _ _ le_xy2.
by apply/(ler_trans _ le1 le2).
qed.

lemma nosmt ltr_pmul (x1 y1 x2 y2 : t):
  zeror <= x1 => zeror <= x2 => x1 < y1 => x2 < y2 => x1 * x2 < y1 * y2.
proof.
move=> x1ge0 x2ge0 lt_xy1 lt_xy2; apply/(@ler_lt_trans (y1 * x2)).
  by apply/ler_wpmul2r/ltrW.
by apply/ltr_pmul2l=> //; apply/(ler_lt_trans _ x1ge0).
qed.

(* -------------------------------------------------------------------- *)
lemma ler_total x y : (x <= y) \/ (y <= x).
proof.
have := real_axiom y; have := real_axiom x.
case: (zeror <= x)=> /= [x_ge0|x_nge0 x_le0]; last first.
  case: (zeror <= y)=> /=; first by move/(ler_trans _ _ _ x_le0)=> ->.
  by move=> _ /(ler_leVge _ _ x_le0).
by case=> [/(ger_leVge _ _ x_ge0) //| /ler_trans ->].
qed.

lemma ltr_total x y : x <> y => (x < y) \/ (y < x).
proof. by rewrite !ltr_def (@eq_sym _ y) => -> /=; apply: ler_total. qed.

lemma nosmt ltrNge (x y : t): (x < y) <=> !(y <= x).
proof.
rewrite ltr_def; have := ler_total x y.
by case: (x <= y)=> //=; rewrite eqr_le => ->.
qed.

lemma nosmt lerNgt (x y : t): (x <= y) <=> !(y < x).
proof. by rewrite ltrNge. qed.

(* -------------------------------------------------------------------- *)
lemma leVge x y : (x <= y) \/ (y <= x).
proof. by case: (x <= y) => // /ltrNge /ltrW. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt ltrN10: -oner < zeror.
proof. by rewrite oppr_lt0 ltr01. qed.

lemma nosmt lerN10: -oner <= zeror.
proof. by rewrite oppr_le0 ler01. qed.

lemma nosmt ltr0N1: !(zeror < -oner).
proof. by rewrite ler_gtF // lerN10. qed.

lemma nosmt ler0N1: !(zeror <= -oner).
proof. by rewrite ltr_geF // ltrN10. qed.

lemma nosmt pmulr_rlt0 (x y : t):
  zeror < x => (x * y < zeror) <=> (y < zeror).
proof.
by move=> x_gt0; rewrite -oppr_gt0 -mulrN pmulr_rgt0 // oppr_gt0.
qed.

lemma nosmt pmulr_rle0 (x y : t):
  zeror < x => (x * y <= zeror) <=> (y <= zeror).
proof.
by move=> x_gt0; rewrite -oppr_ge0 -mulrN pmulr_rge0 // oppr_ge0.
qed.

lemma nosmt pmulr_lgt0 (x y : t):
  zeror < x => (zeror < y * x) <=> (zeror < y).
proof. by move=> x_gt0; rewrite mulrC pmulr_rgt0. qed.

lemma nosmt pmulr_lge0 (x y : t):
  zeror < x => (zeror <= y * x) <=> (zeror <= y).
proof. by move=> x_gt0; rewrite mulrC pmulr_rge0. qed.

lemma nosmt pmulr_llt0 (x y : t):
  zeror < x => (y * x < zeror) <=> (y < zeror).
proof. by move=> x_gt0; rewrite mulrC pmulr_rlt0. qed.

lemma nosmt pmulr_lle0 (x y : t):
  zeror < x => (y * x <= zeror) <=> (y <= zeror).
proof. by move=> x_gt0; rewrite mulrC pmulr_rle0. qed.

lemma nosmt nmulr_rgt0 (x y : t):
  x < zeror => (zeror < x * y) <=> (y < zeror).
proof. by move=> x_lt0; rewrite -mulrNN pmulr_rgt0 lter_oppE. qed.

lemma nosmt nmulr_rge0 (x y : t):
  x < zeror => (zeror <= x * y) <=> (y <= zeror).
proof. by move=> x_lt0; rewrite -mulrNN pmulr_rge0 lter_oppE. qed.

lemma nosmt nmulr_rlt0 (x y : t):
  x < zeror => (x * y < zeror) <=> (zeror < y).
proof. by move=> x_lt0; rewrite -mulrNN pmulr_rlt0 lter_oppE. qed.

lemma nosmt nmulr_rle0 (x y : t):
  x < zeror => (x * y <= zeror) <=> (zeror <= y).
proof. by move=> x_lt0; rewrite -mulrNN pmulr_rle0 lter_oppE. qed.

lemma nosmt nmulr_lgt0 (x y : t):
  x < zeror => (zeror < y * x) <=> (y < zeror).
proof. by move=> x_lt0; rewrite mulrC nmulr_rgt0. qed.

lemma nosmt nmulr_lge0 (x y : t):
  x < zeror => (zeror <= y * x) <=> (y <= zeror).
proof. by move=> x_lt0; rewrite mulrC nmulr_rge0. qed.

lemma nosmt nmulr_llt0 (x y : t):
  x < zeror => (y * x < zeror) <=> (zeror < y).
proof. by move=> x_lt0; rewrite mulrC nmulr_rlt0. qed.

lemma nosmt nmulr_lle0 (x y : t):
  x < zeror => (y * x <= zeror) <=> (zeror <= y).
proof. by move=> x_lt0; rewrite mulrC nmulr_rle0. qed.

lemma nosmt mulr_ge0 (x y : t):
  zeror <= x => zeror <= y => zeror <= x * y.
proof. by move=> x_ge0 y_ge0; rewrite -(mulr0 x) ler_wpmul2l. qed.

lemma nosmt mulr_le0 (x y : t):
  x <= zeror => y <= zeror => zeror <= x * y.
proof. by move=> x_le0 y_le0; rewrite -(mulr0 x) ler_wnmul2l. qed.

lemma nosmt mulr_ge0_le0 (x y : t):
  zeror <= x => y <= zeror => x * y <= zeror.
proof. by move=> x_le0 y_le0; rewrite -(mulr0 x) ler_wpmul2l. qed.

lemma nosmt mulr_le0_ge0 (x y : t):
  x <= zeror => zeror <= y => x * y <= zeror.
proof. by move=> x_le0 y_le0; rewrite -(mulr0 x) ler_wnmul2l. qed.

lemma nosmt mulr_gt0 (x y : t):
  zeror < x => zeror < y => zeror < x * y.
proof. by move=> x_gt0 y_gt0; rewrite pmulr_rgt0. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt ger_pmull x y : zeror < y => (x * y <= y) <=> (x <= oner).
proof. by move=> hy; rewrite -{2}(mul1r y) ler_pmul2r. qed.

lemma nosmt gtr_pmull x y : zeror < y => (x * y < y) <=> (x < oner).
proof. by move=> hy; rewrite -{2}(mul1r y) ltr_pmul2r. qed.

lemma nosmt ger_pmulr x y : zeror < y => (y * x <= y) <=> (x <= oner).
proof. by move=> hy; rewrite -{2}(mulr1 y) ler_pmul2l. qed.

lemma nosmt gtr_pmulr x y : zeror < y => (y * x < y) <=> (x < oner).
proof. by move=> hy; rewrite -{2}(mulr1 y); rewrite ltr_pmul2l. qed.

lemma nosmt ler_pmull x y : zeror < y => (y <= x * y) <=> (oner <= x).
proof. by move=> hy; rewrite -{1}(mul1r y) ler_pmul2r. qed.

lemma nosmt ltr_pmull x y : zeror < y => (y < x * y) <=>(oner < x).
proof. by move=> hy; rewrite -{1}(mul1r y) ltr_pmul2r. qed.

lemma nosmt ler_pmulr x y : zeror < y => (y <= y * x) <=>(oner <= x).
proof. by move=> hy; rewrite -{1}(mulr1 y) ler_pmul2l. qed.

lemma nosmt ltr_pmulr x y : zeror < y => (y < y * x) <=>(oner < x).
proof. by move=> hy; rewrite -{1}(mulr1 y) ltr_pmul2l. qed.

lemma nosmt ger_nmull x y : y < zeror => (x * y <= y) = (oner <= x).
proof. by move=> hy; rewrite -{2}(mul1r y)ler_nmul2r. qed.

lemma nosmt gtr_nmull x y : y < zeror => (x * y < y) = (oner < x).
proof. by move=> hy; rewrite -{2}(mul1r y) ltr_nmul2r. qed.

lemma nosmt ger_nmulr x y : y < zeror => (y * x <= y) = (oner <= x).
proof. by move=> hy; rewrite -{2}(mulr1 y) ler_nmul2l. qed.

lemma nosmt gtr_nmulr x y : y < zeror => (y * x < y) = (oner < x).
proof. by move=> hy; rewrite -{2}(mulr1 y) ltr_nmul2l. qed.

lemma nosmt ler_nmull x y : y < zeror => (y <= x * y) <=> (x <= oner).
proof. by move=> hy; rewrite -{1}(mul1r y) ler_nmul2r. qed.

lemma nosmt ltr_nmull x y : y < zeror => (y < x * y) <=> (x < oner).
proof. by move=> hy; rewrite -{1}(mul1r y) ltr_nmul2r. qed.

lemma nosmt ler_nmulr x y : y < zeror => (y <= y * x) <=> (x <= oner).
proof. by move=> hy; rewrite -{1}(mulr1 y) ler_nmul2l. qed.

lemma nosmt ltr_nmulr x y : y < zeror => (y < y * x) <=> (x < oner).
proof. by move=> hy; rewrite -{1}(mulr1 y) ltr_nmul2l. qed.

(* -------------------------------------------------------------------- *)
lemma ler_pemull x y : zeror <= y => oner <= x => y <= x * y.
proof. by move=> hy hx; rewrite -{1}(mul1r y) ler_wpmul2r. qed.

lemma ler_nemull x y : y <= zeror => oner <= x => x * y <= y.
proof. by move=> hy hx; rewrite -{2}(mul1r y) ler_wnmul2r. qed.

lemma ler_pemulr x y : zeror <= y => oner <= x => y <= y * x.
proof. by move=> hy hx; rewrite -{1}(mulr1 y) ler_wpmul2l. qed.

lemma ler_nemulr x y : y <= zeror => oner <= x => y * x <= y.
proof. by move=> hy hx; rewrite -{2}(mulr1 y) ler_wnmul2l. qed.

lemma nosmt ler_pimull x y : zeror <= y => x <= oner => x * y <= y.
proof. by move=> hy hx; rewrite -{2}(mul1r y) ler_wpmul2r. qed.

lemma nosmt ler_nimull x y : y <= zeror => x <= oner => y <= x * y.
proof. by move=> hy hx; rewrite -{1}(mul1r y) ler_wnmul2r. qed.

lemma nosmt ler_pimulr x y : zeror <= y => x <= oner => y * x <= y.
proof. by move=> hy hx; rewrite -{2}(mulr1 y) ler_wpmul2l. qed.

lemma nosmt ler_nimulr x y : y <= zeror => x <= oner => y <= y * x.
proof. by move=> hx hy; rewrite -{1}(mulr1 y) ler_wnmul2l. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt mulr_ile1 (x y : t):
  zeror <= x => zeror <= y => x <= oner => y <= oner => x * y <= oner.
proof. by move=> ????; rewrite (@ler_trans y) ?ler_pimull. qed.

lemma nosmt mulr_ilt1 (x y : t):
  zeror <= x => zeror <= y => x < oner => y < oner => x * y < oner.
proof. by move=> ????; rewrite (@ler_lt_trans y) ?ler_pimull // ?ltrW. qed.

hint rewrite mulr_ilte1 : mulr_ile1 mulr_ilt1.
hint rewrite mulr_cp1   : mulr_ile1 mulr_ilt1.

(* -------------------------------------------------------------------- *)
lemma mulr_ege1 x y : oner <= x => oner <= y => oner <= x * y.
proof.
by move=> le1x le1y; rewrite (@ler_trans y) ?ler_pemull // (ler_trans _ ler01).
qed.

lemma mulr_egt1 x y : oner < x => oner < y => oner < x * y.
proof.
by move=> le1x lt1y; rewrite (@ltr_trans y) // ltr_pmull // (ltr_trans _ ltr01).
qed.

hint rewrite mulr_egte1 : mulr_ege1  mulr_egt1.
hint rewrite mulr_cp1   : mulr_ege1  mulr_egt1.

(* -------------------------------------------------------------------- *)
lemma nosmt invr_gt0 x : (zeror < invr x) <=> (zeror < x).
proof.
case: (unit x) => [ux|nux]; last by rewrite invr_out.
by split=> /ltr_pmul2r <-; rewrite mul0r (mulrV, mulVr) ?ltr01.
qed.

lemma nosmt invr_ge0 x : (zeror <= invr x) <=> (zeror <= x).
proof. by rewrite !le0r invr_gt0 invr_eq0. qed.

lemma nosmt invr_lt0 x : (invr x < zeror) <=> (x < zeror).
proof. by rewrite -oppr_cp0 -invrN invr_gt0 oppr_cp0. qed.

lemma nosmt invr_le0 x : (invr x <= zeror) <=> (x <= zeror).
proof. by rewrite -oppr_cp0 -invrN invr_ge0 oppr_cp0. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt divr_ge0 x y : zeror <= x => zeror <= y => zeror <= x / y.
proof. by move=> x_ge0 y_ge0; rewrite mulr_ge0 ?invr_ge0. qed.

lemma nosmt divr_gt0 x y : zeror < x => zeror < y => zeror < x / y.
proof. by move=> x_gt0 y_gt0; rewrite pmulr_rgt0 ?invr_gt0. qed.

(* -------------------------------------------------------------------- *)
lemma ler_pinv :
  forall x y, unit x => zeror < x => unit y => zeror < y =>
    (invr y <= invr x) <=> (x <= y).
proof.
move=> x y Ux hx Uy hy; rewrite -(ler_pmul2l hx) -(ler_pmul2r hy).
by rewrite !(divrr, mulrVK) // mul1r.
qed.

lemma ler_ninv :
  forall x y, unit x => x < zeror => unit y => y < zeror =>
    (invr y <= invr x) <=> (x <= y).
proof.
move=> x y Ux hx Uy hy; rewrite -(ler_nmul2l hx) -(ler_nmul2r hy).
by rewrite !(divrr, mulrVK) // mul1r.
qed.

lemma ltr_pinv :
  forall x y, unit x => zeror < x => unit y => zeror < y =>
    (invr y < invr x) <=> (x < y).
proof.
move=> x y Ux hx Uy hy; rewrite -(ltr_pmul2l hx) -(ltr_pmul2r hy).
by rewrite !(divrr, mulrVK) // mul1r.
qed.

lemma ltr_ninv :
  forall x y, unit x => x < zeror => unit y => y < zeror =>
    (invr y < invr x) <=> (x < y).
move=> x y Ux hx Uy hy; rewrite -(ltr_nmul2l hx) -(ltr_nmul2r hy).
by rewrite !(divrr, mulrVK) // mul1r.
qed.

(* -------------------------------------------------------------------- *)
lemma invr_gt1 x : unit x => zeror < x => (oner < invr x) <=> (x < oner).
proof. by move=> Ux gt0_x; rewrite -{1}invr1 ltr_pinv ?unitr1 ?ltr01. qed.

lemma invr_ge1 x : unit x => zeror < x => (oner <= invr x) <=> (x <= oner).
proof. by move=> Ux gt0_x; rewrite -{1}invr1 ler_pinv ?unitr1 ?ltr01. qed.

hint rewrite invr_gte1 : invr_ge1 invr_gt1.
hint rewrite invr_cp1  : invr_ge1 invr_gt1.

lemma invr_le1 x : unit x => zeror < x => (invr x <= oner) <=> (oner <= x).
proof. by move=> ux hx; rewrite -invr_ge1 ?invr_gt0 ?unitrV // invrK. qed.

lemma invr_lt1 x : unit x => zeror < x => (invr x < oner) <=> (oner < x).
proof. by move=> ux hx; rewrite -invr_gt1 ?invr_gt0 ?unitrV // invrK. qed.

hint rewrite invr_lte1 : invr_le1 invr_lt1.
hint rewrite invr_cp1  : invr_le1 invr_lt1.

(* -------------------------------------------------------------------- *)
lemma expr_ge0 n x : zeror <= x => zeror <= exp x n.
proof.
move=> ge0_x; elim/intwlog: n.
+ by move=> n; rewrite exprN invr_ge0.
+ by rewrite expr0 ler01.
+ by move=> n ge0_n ge0_e; rewrite exprS // mulr_ge0.
qed.

lemma expr_gt0 n x : zeror < x => zeror < exp x n.
proof. by rewrite !lt0r expf_eq0 => -[->/=]; apply/expr_ge0. qed.

hint rewrite expr_gte0 : expr_ge0 expr_gt0.

lemma nosmt exprn_ile1 n x : 0 <= n => zeror <= x <= oner => exp x n <= oner.
proof.
move=> nge0 [xge0 xle1]; elim: n nge0; 1: by rewrite expr0.
by move=> n ge0_n ih; rewrite exprS // mulr_ile1 ?expr_ge0.
qed.

lemma nosmt exprn_ilt1 n x :
  0 <= n => zeror <= x < oner => (exp x n < oner) <=> (n <> 0).
proof.
move=> nge0 [xge0 xlt1]; case: n nge0; 1: by rewrite expr0 ltrr.
move=> n nge0 _; rewrite addz_neq0 //=; elim: n nge0; 1: by rewrite expr1.
by move=> n nge0 ih; rewrite exprS 1:addz_ge0 // mulr_ilt1 ?expr_ge0.
qed.

hint rewrite exprn_ilte1 : exprn_ile1 exprn_ilt1.
hint rewrite exprn_cp1   : exprn_ile1 exprn_ilt1.

lemma nosmt exprn_ege1 n x : 0 <= n => oner <= x => oner <= exp x n.
proof.
move=> nge0 xge1; elim: n nge0 => [|n nge0 ih]; 1: by rewrite expr0.
by rewrite exprS // mulr_ege1.
qed.

lemma nosmt exprn_egt1 n x : 0 <= n => oner < x => (oner < exp x n) <=> (n <> 0).
proof.
move=> nge0 xgt1; case: n nge0 => [|n nge0 _]; 1: by rewrite expr0 ltrr.
elim: n nge0 => [|n ge0n]; 1: by rewrite expr1.
rewrite !addz1_neq0 ?addz_ge0 //= => ih.
by rewrite (@exprS _ (n+1)) 1:addz_ge0 // mulr_egt1.
qed.

hint rewrite exprn_egte1 : exprn_ege1 exprn_egt1.
hint rewrite exprn_cp1   : exprn_ege1 exprn_egt1.

lemma nosmt ler_iexpr x n : 0 < n => zeror <= x <= oner => exp x n <= x.
proof.
rewrite ltz_def => -[nz_n ge0_n]; case: n ge0_n nz_n => // n ge0_n _ _.
by case=> xge0 xlt1; rewrite exprS // ler_pimulr // exprn_ile1.
qed.

lemma nosmt ltr_iexpr x n : 0 <= n => zeror < x < oner => (exp x n < x <=> 1 < n).
proof.
move=> nge0 [xgt0 xlt1]; case: n nge0 => /= [|n nge0 _].
+ by rewrite expr0 ltrNge ltrW.
case: n nge0 => /= [|n nge0 _]; first by rewrite expr1 ltrr.
rewrite (@ltz_add2r 1 0 (n+1)) -lez_add1r /= lez_addr nge0 /=.
rewrite (@exprS _ (n+1)) 1:addz_ge0 // gtr_pmulr //.
by rewrite exprn_ilt1 ?(addz_neq0, addz_ge0) // ltrW.
qed.

hint rewrite lter_iexpr : ler_iexpr ltr_iexpr.
hint rewrite lter_expr  : ler_iexpr ltr_iexpr.

lemma nosmt ler_eexpr x n : 0 < n => oner <= x => x <= exp x n.
proof.
rewrite ltz_def => -[nz_n ge0_n]; case: n ge0_n nz_n => //=.
move=> n ge0_n _ _ ge1_x; rewrite exprS //.
by rewrite ler_pemulr 2:exprn_ege1 // &(@ler_trans oner) ?ler01.
qed.

lemma nosmt ltr_eexpr x n : 0 <= n => oner < x => (x < exp x n <=> 1 < n).
proof.
move=> ge0_n lt1_x; case: n ge0_n; 1: by rewrite expr0 ltrNge ltrW.
move=> + + _; case=> /= [|n ge0_n _]; first by rewrite expr1 ltrr.
rewrite (@ltz_add2r 1 0 (n+1)) -lez_add1r /= lez_addr ge0_n /=.
rewrite (@exprS _ (n+1)) 1:addz_ge0 // ltr_pmulr 1:&(@ltr_trans oner) //.
by rewrite exprn_egt1 // ?(addz_neq0, addz_ge0).
qed.

hint rewrite lter_eexpr : ler_eexpr  ltr_eexpr.
hint rewrite lter_expr  : ler_eexpr  ltr_eexpr.

lemma nosmt ler_wiexpn2l x : zeror <= x <= oner =>
  forall m n, 0 <= n <= m => exp x m <= exp x n.
proof.
move=> [xge0 xle1] m n [ge0_n le_nm]; have ->: m = (m - n) + n by ring.
by rewrite exprDn 1:subz_ge0 // ler_pimull ?(expr_ge0, exprn_ile1) ?subz_ge0.
qed.

lemma nosmt ler_weexpn2l x : oner <= x =>
  forall m n, 0 <= m <= n => exp x m <= exp x n.
proof.
move=> ge1_x m n [ge0_m le_mn]; have ->: n = (n - m) + m by ring.
rewrite exprDn 1:subz_ge0 // ler_pemull ?(expr_ge0, exprn_ege1) //.
+ by rewrite (@ler_trans oner). + by rewrite subz_ge0.
qed.

lemma nosmt ieexprn_weq1 x n : 0 <= n => zeror <= x =>
  (exp x n = oner) <=> (n = 0 || x = oner).
proof.
case: n => [|n ge0_n _] ge0_x; first by rewrite expr0.
rewrite !addz_neq0 //=; split=> [|->]; last by rewrite expr1z.
case: (x = oner) => [->//|/ltr_total [] hx] /=.
+ by rewrite ltr_eqF // exprn_ilt1 // (addz_ge0, addz_neq0).
+ by rewrite gtr_eqF // exprn_egt1 // (addz_ge0, addz_neq0).
qed.

lemma nosmt ieexprIn x : zeror < x => x <> oner =>
  forall m n, 0 <= m => 0 <= n => exp x m = exp x n => m = n.
proof.
(* FIXME: wlog *)
move=> gt0_x neq1_x m n; pose P := fun m n => 0 <= m => 0 <= n =>
  exp x m = exp x n => m = n; rewrite -/(P m n).
have: (forall m n, (m <= n)%Int => P m n) => P m n.
+ move=> ih; case: (lez_total m n); first by apply/ih.
  by move/ih=> @/P h *; rewrite -h // eq_sym.
apply=> {m n} m n le_mn ge0_m ge0_n {P}.
have ->: n = m + (n - m) by ring.
rewrite exprDn 2:subz_ge0 // -{1}(mulr1 (exp x m)).
have h/h{h} := mulfI (exp x m) _; first by rewrite expf_eq0 gtr_eqF.
by rewrite eq_sym ieexprn_weq1 1?(subz_ge0, ltrW) //#.
qed.

lemma nosmt ler_pexp n x y :
  0 <= n => zeror <= x <= y => exp x n <= exp y n.
proof.
move=> h; elim/intind: n h x y => [|n ge0_n ih] x y [ge0_x le_xy].
+ by rewrite !expr0.
+ by rewrite !exprS // ler_pmul // ?expr_ge0 ?ih.
qed.

lemma nosmt ge0_sqr (x : t) : zeror <= exp x 2.
proof.
rewrite expr2; case: (zeror <= x); first by move=> h; apply/mulr_ge0.
by rewrite lerNgt /= => /ltrW le0_x; apply/mulr_le0.
qed.

(* -------------------------------------------------------------------- *)
lemma nosmt ler_norm_sub (x y : t):
  `|x - y| <= `|x| + `|y|.
proof. by rewrite -(@normrN y) ler_norm_add. qed.

lemma nosmt ler_dist_add (z x y : t):
  `|x - y| <= `|x - z| + `|z - y|.
proof.                          (* FIXME *)
apply/(ler_trans _ _ (:@ler_norm_add (x-z) (z-y))).
by rewrite addrA addrNK lerr.
qed.

lemma nosmt ler_sub_norm_add (x y : t):
  `|x| - `|y| <= `|x + y|.
proof.
rewrite -{1}(@addrK y x) lter_sub_addl;
  rewrite (ler_trans _ (:@ler_norm_add (x+y) (-y))) //.
by rewrite addrC normrN lerr.
qed.

lemma nosmt ler_sub_dist (x y : t):
  `|x| - `|y| <= `|x - y|.
proof. by rewrite -(@normrN y) ler_sub_norm_add. qed.

lemma nosmt ler_dist_dist (x y : t):
  `| `|x| - `|y| | <= `|x - y|.
proof.                          (* FIXME *)
case: (`|x| <= `|y|); last first.
  rewrite -ltrNge=> /ltrW le_yx;
    by rewrite ger0_norm ?ler_sub_dist // subr_ge0.
move=> le_xy; rewrite ler0_norm ?subr_le0 //.
by rewrite distrC opprB  ler_sub_dist.
qed.

lemma nosmt ler_dist_norm_add (x y : t):
  `| `|x| - `|y| | <= `|x + y|.
proof. by rewrite -(@opprK y) normrN ler_dist_dist. qed.

lemma nosmt ler_nnorml (x y : t): y < zeror => ! (`|x| <= y).
proof. by move=> y_lt0; rewrite ltr_geF // (ltr_le_trans _ y_lt0) ?normr_ge0. qed.

lemma nosmt ltr_nnorml (x y : t): y <= zeror => ! (`|x| < y).
proof. by move=> y_le0; rewrite ler_gtF // (ler_trans _ y_le0) ?normr_ge0. qed.

lemma nosmt eqr_norm_id (x : t): (`|x| = x) <=> (zeror <= x).
proof. by rewrite ger0_def. qed.

lemma nosmt eqr_normN (x : t): (`|x| = - x) <=> (x <= zeror).
proof. by rewrite ler0_def. qed.

(* -------------------------------------------------------------------- *)
lemma ler_norm x : x <= `|x|.
proof.
case: (zeror <= x); first by move/ger0_norm=> ->; apply/lerr.
move/ltrNge=> /ltrW ^h /ler0_norm ->; apply/(ler_trans zeror)=> //.
by rewrite oppr_ge0.
qed.

lemma eqr_norml x y : (`|x| = y) <=> ((x = y) \/ (x = -y)) /\ (zeror <= y).
proof.
split=> [|[]]; last by case=> -> h; rewrite ?normrN ger0_norm.
move=> <-; rewrite normr_ge0 /=; case: (x <= zeror) => [|/ltrNge].
  by move/ler0_norm=> ->; rewrite opprK.
by move/gtr0_norm=> ->.
qed.

(* -------------------------------------------------------------------- *)
lemma nosmt ler_norml x y : (`|x| <= y) <=> (- y <= x <= y).
proof.
have h: forall z, zeror <= z => (z <= y) <=> (- y <= z <= y).
  move=> z ge0_z; case: (z <= y)=> //= le_zy; apply/(ler_trans zeror)=> //.
  by rewrite oppr_le0 (ler_trans z).
case: (zeror <= x) => [^ge0_x /h|/ltrNge/ltrW ge0_x]; first by rewrite ger0_norm.
rewrite -(opprK x) normrN ler_opp2 andaE andbC ler_oppl h.
  by rewrite normr_ge0. by rewrite ger0_norm // oppr_ge0.
qed.

lemma nosmt ltr_normr x y : (x < `|y|) <=> (x < y) \/ (x < - y).
proof. by rewrite ltrNge ler_norml andaE negb_and -!ltrNge ltr_oppr orbC. qed.

lemma ltr_norml : forall x y, (`|x| < y) <=> (- y < x < y).
proof.
have h:
  (forall x y, zeror <= x => (`|x| < y) <=> (- y < x < y))
  => forall x y, (`|x| < y) <=> (- y < x < y).
+ move=> wlog x y; case: (leVge zeror x) => [/wlog|hx]; 1: by apply.
  rewrite -(opprK x) normrN wlog ?oppr_ge0 //.
  by rewrite !ltr_opp2 !andaE andbC opprK.
apply/h=> x y hx; rewrite ger0_norm //; case: (x < y) => //= le_xy.
by rewrite (ltr_le_trans _ _ hx) oppr_lt0 (ler_lt_trans _ hx).
qed.

lemma nosmt ler_normr x y : (x <= `|y|) <=> (x <= y) \/ (x <= - y).
proof.
by rewrite lerNgt ltr_norml // andaE negb_and !lerNgt orbC ltr_oppl.
qed.

(* -------------------------------------------------------------------- *)
lemma maxrC (x y : t) : maxr x y = maxr y x.
proof. by rewrite !maxrE lerNgt ler_eqVlt; case: (x = y); case: (x < y). qed.

lemma maxrl (x y : t) : x <= maxr x y.
proof. by rewrite maxrE; case: (y <= x) => [_|/ltrNge/ltrW]. qed.

lemma maxrr (x y : t) : y <= maxr x y.
proof. by rewrite maxrC maxrl. qed.

lemma ler_maxr (x y : t) : x <= y => maxr x y = y.
proof. by rewrite maxrE lerNgt ler_eqVlt => -> /#. qed.

lemma ler_maxl (x y : t) : y <= x => maxr x y = x.
proof. by rewrite maxrC &(ler_maxr). qed.

lemma maxr_ub (x y : t) : x <= maxr x y /\ y <= maxr x y.
proof. by rewrite maxrl maxrr. qed.

lemma ler_maxrP m n1 n2 : (maxr n1 n2 <= m) <=> (n1 <= m) /\ (n2 <= m).
proof. 
split; last by case=> le1 le2; rewrite maxrE; case: (n2 <= n1).
rewrite maxrE; case: (n2 <= n1).
* by move=> le_21 le_n1m; rewrite (ler_trans _ le_21 le_n1m).
* rewrite lerNgt /= => /ltrW le_12 le_n1m.
  by rewrite (ler_trans _ le_12 le_n1m).
qed.

lemma ltr_maxrP m n1 n2 : (maxr n1 n2 < m) <=> (n1 < m) /\ (n2 < m).
proof.
split; last by case=> le1 le2; rewrite maxrE; case: (n2 <= n1).
rewrite maxrE; case: (n2 <= n1).
* by move=> le_21 lt_n1m; rewrite (ler_lt_trans _ le_21 lt_n1m).
* rewrite lerNgt /= => lt_12 lt_n1m.
  by rewrite (ltr_trans _ lt_12 lt_n1m).
qed.
end RealDomain.

(* -------------------------------------------------------------------- *)
theory RealField.
type t.

clone import Ring.Field as Field with type t <- t.
clear [Field.* Field.AddMonoid.* Field.MulMonoid.*].

clone include RealDomain with type t <- t,
  pred Domain.unit (x : t) <- x <> zeror,
  op   Domain.zeror  <- Field.zeror,
  op   Domain.oner   <- Field.oner,
  op   Domain.( + )  <- Field.( + ),
  op   Domain.([-])  <- Field.([-]),
  op   Domain.( * )  <- Field.( * ),
  op   Domain.invr   <- Field.invr,
  op   Domain.intmul <- Field.intmul,
  op   Domain.ofint  <- Field.ofint,
  op   Domain.exp    <- Field.exp

  proof Domain.*
  remove abbrev Domain.(-)
  remove abbrev Domain.(/).

  realize  Domain.addrA     by apply/Field.addrA    .
  realize  Domain.addrC     by apply/Field.addrC    .
  realize  Domain.add0r     by apply/Field.add0r    .
  realize  Domain.addNr     by apply/Field.addNr    .
  realize  Domain.oner_neq0 by apply/Field.oner_neq0.
  realize  Domain.mulrA     by apply/Field.mulrA    .
  realize  Domain.mulrC     by apply/Field.mulrC    .
  realize  Domain.mul1r     by apply/Field.mul1r    .
  realize  Domain.mulrDl    by apply/Field.mulrDl   .
  realize  Domain.mulVr     by apply/Field.mulVr    .
  realize  Domain.unitP     by apply/Field.unitP    .
  realize  Domain.unitout   by apply/Field.unitout  .
  realize  Domain.mulf_eq0  by apply/Field.mulf_eq0 .

(* -------------------------------------------------------------------- *)
lemma lef_pinv x y :
  zeror < x => zeror < y => (invr y <= invr x) <=> (x <= y).
proof. by move=> hx hy; apply/ler_pinv=> //; apply/gtr_eqF. qed.

lemma lef_ninv x y :
  x < zeror => y < zeror => (invr y <= invr x) <=> (x <= y).
proof. by move=> hx hy; apply/ler_ninv=> //; apply/ltr_eqF. qed.

lemma ltf_pinv x y :
  zeror < x => zeror < y => (invr y < invr x) <=> (x < y).
proof. by move=> hx hy; apply/ltr_pinv=> //; apply/gtr_eqF. qed.

lemma ltf_ninv x y :
  x < zeror => y < zeror => (invr y < invr x) <=> (x < y).
proof. by move=> hx hy; apply/ltr_ninv=> //; apply/ltr_eqF. qed.

(* -------------------------------------------------------------------- *)
lemma ler_pdivl_mulr z x y : zeror < z => (x <= y / z) <=> (x * z <= y).
proof. by move=> z_gt0; rewrite -(@ler_pmul2r z) ?mulrVK ?gtr_eqF //. qed.

lemma ltr_pdivl_mulr z x y : zeror < z => (x < y / z) <=> (x * z < y).
proof. by move=> z_gt0; rewrite -(@ltr_pmul2r z) ?mulrVK ?gtr_eqF. qed.

hint rewrite lter_pdivl_mulr : ler_pdivl_mulr ltr_pdivl_mulr.

(* -------------------------------------------------------------------- *)
lemma ler_pdivr_mulr z x y : zeror < z => (y / z <= x) <=> (y <= x * z).
proof. by move=> z_gt0; rewrite -(@ler_pmul2r z) ?mulrVK ?gtr_eqF. qed.

lemma ltr_pdivr_mulr z x y : zeror < z => (y / z < x) <=> (y < x * z).
proof. by move=> z_gt0; rewrite -(@ltr_pmul2r z) ?mulrVK ?gtr_eqF. qed.

hint rewrite lter_pdivr_mulr : ler_pdivr_mulr ltr_pdivr_mulr.

(* -------------------------------------------------------------------- *)
lemma ler_pdivl_mull z x y : zeror < z => (x <= invr z * y) <=> (z * x <= y).
proof. by move=> z_gt0; rewrite mulrC ler_pdivl_mulr ?(mulrC z). qed.

lemma ltr_pdivl_mull z x y : zeror < z => (x < invr z * y) <=> (z * x < y).
proof. by move=> z_gt0; rewrite mulrC ltr_pdivl_mulr ?(mulrC z). qed.

hint rewrite lter_pdivl_mull : ler_pdivl_mull ltr_pdivl_mull.

(* -------------------------------------------------------------------- *)
lemma ler_pdivr_mull z x y : zeror < z => (invr z * y <= x) <=> (y <= z * x).
proof. by move=> z_gt0; rewrite mulrC ler_pdivr_mulr ?(mulrC z). qed.

lemma ltr_pdivr_mull z x y : zeror < z => (invr z * y < x) <=> (y < z * x).
proof. by move=> z_gt0; rewrite mulrC ltr_pdivr_mulr ?(mulrC z). qed.

hint rewrite lter_pdivr_mull : ler_pdivr_mull ltr_pdivr_mull.

(* -------------------------------------------------------------------- *)
lemma ler_ndivl_mulr z x y : z < zeror => (x <= y / z) <=> (y <= x * z).
proof. by move=> z_lt0; rewrite -(@ler_nmul2r z) ?mulrVK  ?ltr_eqF. qed.

lemma ltr_ndivl_mulr z x y : z < zeror => (x < y / z) <=> (y < x * z).
proof. by move=> z_lt0; rewrite -(@ltr_nmul2r z) ?mulrVK ?ltr_eqF. qed.

hint rewrite lter_ndivl_mulr : ler_ndivl_mulr ltr_ndivl_mulr.

(* -------------------------------------------------------------------- *)
lemma ler_ndivr_mulr z x y : z < zeror => (y / z <= x) <=> (x * z <= y).
proof. by move=> z_lt0; rewrite -(@ler_nmul2r z) ?mulrVK ?ltr_eqF. qed.

lemma ltr_ndivr_mulr z x y : z < zeror => (y / z < x) <=> (x * z < y).
proof. by move=> z_lt0; rewrite -(@ltr_nmul2r z) ?mulrVK ?ltr_eqF. qed.

hint rewrite lter_ndivr_mulr : ler_ndivr_mulr ltr_ndivr_mulr.

(* -------------------------------------------------------------------- *)
lemma ler_ndivl_mull z x y : z < zeror => (x <= invr z * y) <=> (y <= z * x).
proof. by move=> z_lt0; rewrite mulrC ler_ndivl_mulr ?(mulrC z). qed.

lemma ltr_ndivl_mull z x y : z < zeror => (x < invr z * y) <=> (y < z * x).
proof. by move=> z_lt0; rewrite mulrC ltr_ndivl_mulr ?(mulrC z). qed.

hint rewrite lter_ndivl_mull : ler_ndivl_mull ltr_ndivl_mull.

(* -------------------------------------------------------------------- *)
lemma ler_ndivr_mull z x y : z < zeror => (invr z * y <= x) <=> (z * x <= y).
proof. by move=> z_lt0; rewrite mulrC ler_ndivr_mulr ?(mulrC z). qed.

lemma ltr_ndivr_mull z x y : z < zeror => (invr z * y < x) <=> (z * x < y).
proof. by move=> z_lt0; rewrite mulrC ltr_ndivr_mulr ?(mulrC z). qed.

hint rewrite lter_ndivr_mull : ler_ndivr_mull ltr_ndivr_mull.
end RealField.
