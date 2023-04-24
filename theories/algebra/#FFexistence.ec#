(* ==================================================================== *)
require import AllCore List Ring Int IntMin IntDiv Real RealExp Poly.
require import StdBigop StdPoly Binomial Counting Perms.
require import RingStruct SubRing PolyDiv FiniteRing Ideal.
(*---*) import StdOrder.IntOrder.



abstract theory FFexistence.
(*
type t, et.

op n : int.

axiom lt0n: 0 < n.

clone import Field as F with
  type t <= t.

clone import FiniteField as FF with
  type t <= t,
  theory F <= F.

clone import SubFiniteField_ZMod as SFF_ZM with
  type t <= t,
  theory F <= F,
  theory FF <= FF.

clone import PolyFF as PFF with
  type coeff <= t,
  theory FF <= FF.

import Counting_Argument.

op is_extension_params1 (mp : int * PID.poly) =
  0 < mp.`1 /\
  PID.irreducible_poly mp.`2 /\
  PID.P.monic mp.`2 /\
  0 < I n (FF.FinType.card ^ (PID.P.deg mp.`2 - 1)).

op m = (choiceb (is_extension_params1) (0, PID.P.poly0)).`1.

op p = (choiceb (is_extension_params1) (0, PID.P.poly0)).`2.

lemma mpP :
  0 < m /\
  PID.irreducible_poly p /\
  PID.P.monic p /\
  0 < I n (FF.FinType.card ^ (PID.P.deg p - 1)).
proof.
move: (choicebP is_extension_params1 (0, PID.P.poly0) _); last first.
+ by rewrite /m /p; pose c:= choiceb _ _; move: c => c; rewrite /is_extension_params1.
rewrite /is_extension_params1; case: (lt0I _ lt0n) => q.
move: (ilog_eq _ (max 1 q) (ilog FF.FinType.card (max 1 q)) card_gt1 _ _) => /=.
+ by apply/gtr_maxrP.
+ by apply/ilog_ge0; [apply/ltzW/card_gt1|apply/ger_maxrP].
rewrite /FF.FinType.card /=.
case=> _ /ltr_maxrP [] _ /ltzW leq_ lt0I_.
case: (exists_iu_le_deg (ilog FinType.card (max 1 q) + 1)) => p.
case=> /ltr_subr_addr /ltzE le_ [] irr_ m_; exists (n, p) => /=.
rewrite lt0n irr_ m_ /=; apply/lt0I_/(ler_trans _ _ _ leq_)/ler_weexpn2l.
+ by apply/ltzW/card_gt1.
rewrite le_ /=; apply/addr_ge0 => //.
by apply/ilog_ge0; [apply/ltzW/card_gt1|apply/ger_maxrP].
qed.

lemma lt0m : 0 < m.
proof. by case: mpP. qed.

lemma irredp_p : PID.irreducible_poly p.
proof. by case: mpP. qed.

lemma monic_p : PID.P.monic p.
proof. by case: mpP. qed.

lemma lt0In_ : 0 < I n (FF.FinType.card ^ (PID.P.deg p - 1)).
proof. by case: mpP. qed.

clone import FFIrrPolyExt as Ext1 with
  type t <= t,
  theory FF <= FF,
  (*FIXME: Pierre-Yves: anomaly here if using the big clone with theory.*)
  (*theory PFF <- PFF.*)
  (*theory PFF.PID.CR <- PFF.PID.CR.*)
  type PFF.PID.poly <= FFexistence.PFF.PID.poly,
  theory PFF.PID.P <= PFF.PID.P,
  theory PFF.PID.PS <= PFF.PID.PS,
  theory PFF.PID.RPD <= PFF.PID.RPD,
  theory PFF.PID.CRD <= PFF.PID.CRD,
  theory PFF.PID.RM <= PFF.PID.RM,
  theory PFF.PID.CR.PCR <= PFF.PID.CR.PCR,
  theory PFF.PID.CR.RPD <= PFF.PID.CR.RPD,
  theory PFF.PID.CR.CRD <= PFF.PID.CR.CRD,
  theory PFF.PID.CR.RM <= PFF.PID.CR.RM,
  op PFF.PID.CR.unit <= FFexistence.PFF.PID.CR.unit,
  op PFF.PID.irreducible_poly <= FFexistence.PFF.PID.irreducible_poly,
  op p <= p
proof PFF.PID.CR.unitP, irredp_p.

realize PFF.PID.CR.unitP by exact FFexistence.PFF.PID.CR.unitP.
realize irredp_p by exact irredp_p.

clone import PolyFF as PFFE with
  type coeff <= Ext1.pt,
  theory FF <= Ext1.FFQ.

op is_extension_params2 (q : PFFE.PID.poly) =
  PFFE.PID.P.deg q = n + 1 /\
  PFFE.PID.irreducible_poly q /\
  PFFE.PID.P.monic q.

op q = choiceb is_extension_params2 PFFE.PID.P.poly0.

lemma qP : is_extension_params2 q.
proof.
rewrite /q; apply/choicebP; rewrite /is_extension_params2.
move: (PFFE.eqI_size_enum_iudeg _ lt0n) lt0In_.
rewrite -cardP => -> /has_predT /hasP [q] [] + _.
by case/enum_iudegP => irr_ [] m_ eq_; exists q.
qed.

lemma eq_degq : PFFE.PID.P.deg q = n + 1.
proof. by case: qP. qed.

lemma irredp_q : PFFE.PID.irreducible_poly q.
proof. by case: qP. qed.

lemma monic_q : PFFE.PID.P.monic q.
proof. by case: qP. qed.

clone import FFIrrPolyExt as Ext2 with
  type t <= pt,
  theory FF <= Ext1.FFQ,
  type PFF.PID.poly <= FFexistence.PFFE.PID.poly,
  theory PFF.PID.P <= PFFE.PID.P,
  theory PFF.PID.PS <= PFFE.PID.PS,
  theory PFF.PID.RPD <= PFFE.PID.RPD,
  theory PFF.PID.CRD <= PFFE.PID.CRD,
  theory PFF.PID.RM <= PFFE.PID.RM,
  theory PFF.PID.CR.PCR <= PFFE.PID.CR.PCR,
  theory PFF.PID.CR.RPD <= PFFE.PID.CR.RPD,
  theory PFF.PID.CR.CRD <= PFFE.PID.CR.CRD,
  theory PFF.PID.CR.RM <= PFFE.PID.CR.RM,
  op PFF.PID.CR.unit <= FFexistence.PFFE.PID.CR.unit,
  op PFF.PID.irreducible_poly <= FFexistence.PFFE.PID.irreducible_poly,
  op p <= q
  (*, theory SubFStr.SFStr <= Ext1.SFF.FStr*)
proof PFF.PID.CR.unitP, irredp_p.
(*TODO: anomaly here if using the big clone with theory.*)
(*theory PFF <- PFF*)
(*theory PFF.PID.CR <- PFF.PID.CR*)

realize PFF.PID.CR.unitP by exact FFexistence.PFFE.PID.CR.unitP.
realize irredp_p by exact irredp_q.

clone import FieldStruct as FStrExt2 with
  type t <= Ext2.pt,
  theory F <= Ext2.FFQ.F.

clone import FiniteFieldStruct as FFStrExt2 with
  type t <= Ext2.pt,
  theory F <= Ext2.FFQ.F,
  theory FStr <= FStrExt2,
  theory FF.FinType <= Ext2.FFQ.FinType.

clone import SubFiniteField as SubFFExt2 with
  type t <= Ext2.pt,
  type st <= et,
  theory F <= Ext2.FFQ.F,
  theory FStr <= FFexistence.FStrExt2,
  theory FF.FinType <= Ext2.FFQ.FinType,
  op SubF.p <= FFexistence.FStrExt2.iter_frobenius_fixed (n * SFF_ZM.SFF.n)
proof SubF.fieldp.

realize SubF.fieldp.
proof.
pose n:= Int.( * ) _ _; move: n => n; rewrite /iter_frobenius_fixed.
split; split; split; [split| | |] => /=.
+ case (0 <= n) => [le0n|/ltrNge/ltzW len0]; [|by rewrite !iter0].
  rewrite iter_frobenius ?le0n // IFQ.FQ.expr0z gtr_eqF //.
  by apply/expr_gt0/gt0_char.
+ move=> x; case (0 < n) => [lt0n|/lerNgt len0]; [|by rewrite !iter0].
  rewrite !iter_frobenius; [by apply/ltzW|by apply/ltzW|].
  rewrite -(IFQ.FQ.mulN1r x).
  move: (IFQ.FQ.expfM (IFQ.([-]) IFQ.oner) x (char ^ n)).
  (*FIXME: Pierre-Yves: the following should not hang:*)
  (*move=> ->.*)
  move=> + eq_; move=> ->; congr => // {eq_}.
  rewrite -FFQ.F.signr_odd ?ltzW ?expr_gt0 ?gt0_char //.
  rewrite poddX ?lt0n //; case/prime_or_2_odd: prime_char.
  - move=> eq_; rewrite eq_ oddP /= b2i0 IFQ.FQ.expr0.
    rewrite -IFQ.FQ.subr_eq0 IFQ.FQ.opprK -IFQ.FQ.mul1r2z IFQ.FQ.mul1r.
    by move: ofint_char; rewrite eq_.
  by move=> ->; rewrite b2i1 IFQ.FQ.expr1.
+ move=> x y; have ->: iter n frobenius (IFQ.(+) x y) = IFQ.(+) (iter n frobenius x) (iter n frobenius y).
  - case (0 <= n) => [|/ltrNge/ltzW len0]; [|by rewrite !iter0].
    elim: n => [|n le0n IHn]; [by rewrite !iter0|].
    by rewrite !iterS //; move: IHn => ->; rewrite frobeniusD // prime_char.
  by move=> -> ->.
+ case (0 <= n) => [le0n|/ltrNge/ltzW len0]; [|by rewrite !iter0].
  by rewrite iter_frobenius ?le0n // FFQ.F.expr1z.
+ move=> x y; have ->: iter n frobenius (IFQ.( * ) x y) = IFQ.( * ) (iter n frobenius x) (iter n frobenius y).
  - case (0 <= n) => [|/ltrNge/ltzW len0]; [|by rewrite !iter0].
    elim: n => [|n le0n IHn]; [by rewrite !iter0|].
    by rewrite !iterS //; move: IHn => ->; rewrite frobeniusM // prime_char.
  by move=> -> ->.
move=> x; case (0 <= n) => [le0n|/ltrNge/ltzW len0]; [|by rewrite !iter0].
move=> {2}<-; rewrite !iter_frobenius ?le0n //; apply/IFQ.FQ.exprVn.
by apply/ltzW/expr_gt0/gt0_char.
qed.

clone import FieldStruct as FStr with
  type t <= et,
  theory F <= SubFFExt2.SubF.SF.

clone import FiniteFieldStruct as FFStr with
  type t <= et,
  theory F <= SubFFExt2.SubF.SF,
  theory FStr <= FStr,
  theory FF.FinType <= SubFFExt2.SFT.

clone import SubFieldStruct as SubFStrExt2 with
  type t <= Ext2.pt,
  type st <= et,
  theory SubZMod <= FFexistence.SubFFExt2.SubF,
  theory SubCR <= FFexistence.SubFFExt2.SubF,
  theory SubID <= FFexistence.SubFFExt2.SubF,
  theory SubF <= FFexistence.SubFFExt2.SubF,
  theory SZModStr <= FFexistence.FStr,
  theory SCRStr <= FFexistence.FStr,
  theory SIDStr <= FFexistence.FStr,
  theory SFStr <= FFexistence.FStr.

op p_ x =
  let y = SubFFExt2.SubF.Sub.val x in
  Ext2.SubFF.SubF.p y /\
  let z = Ext2.SubFF.SubF.Sub.insubd y in
  Ext1.SubFF.SubF.p z.

op insub_ x =
  let y = SubFFExt2.SubF.Sub.val x in
  if Ext2.SubFF.SubF.p y
  then
    let z = Ext2.SubFF.SubF.Sub.insubd y in
    if Ext1.SubFF.SubF.p z
    then Some (Ext1.SubFF.SubF.Sub.insubd z)
    else None
  else None.

op val_ =
  SubFFExt2.SubF.Sub.insubd \o
  Ext2.SubFF.SubF.Sub.val \o
  Ext1.SubFF.SubF.Sub.val.

op wsT_ = val_ witness.

clone import SubFiniteField as SubFF with
  type t <= FFexistence.et,
  type st <= FFexistence.t,
  theory F <= SubFFExt2.SubF.SF,
  theory FStr <= FFexistence.FStr,
  theory FF.FinType <= SubFFExt2.SFT,
  op SubF.p <= p_,
  op SubF.Sub.insub <= insub_,
  op SubF.Sub.val <= val_,
  op SubF.Sub.wsT <= wsT_
proof SubF.fieldp, SubF.Sub.*.

realize SubF.fieldp.
proof.
move: Ext1.SubFF.SubF.fieldp Ext2.SubFF.SubF.fieldp.
rewrite -/Ext1.SubFF.SubF.p -/Ext2.SubFF.SubF.p /p_.
case; case; case=> [] [] p10 p1N p1D p11 p1M p1V.
case; case; case=> [] [] p20 p2N p2D p21 p2M p2V.
split; split; split; [split| | |] => /=.
+ by rewrite SubFFExt2.SubF.val0 p20 Ext2.SubFF.SubF.insubd0 Ext2.eq0 p10.
+ move=> x; rewrite SubFFExt2.SubF.valN => -[] p2x p1x; rewrite p2N //.
  by rewrite Ext2.SubFF.SubF.insubdN // Ext2.eqN p1N.
+ move=> x y; rewrite SubFFExt2.SubF.valD => -[] p2x p1x [] p2y p1y; rewrite p2D //.
  by rewrite Ext2.SubFF.SubF.insubdD // Ext2.eqD p1D.
+ by rewrite SubFFExt2.SubF.val1 p21 Ext2.SubFF.SubF.insubd1 Ext2.eq1 p11.
+ move=> x y; rewrite SubFFExt2.SubF.valM => -[] p2x p1x [] p2y p1y; rewrite p2M //.
  by rewrite Ext2.SubFF.SubF.insubdM // Ext2.eqM p1M.
move=> x; rewrite SubFFExt2.SubF.valV => -[] p2x p1x; rewrite p2V //.
by rewrite Ext2.SubFF.SubF.insubdV // Ext2.eqV p1V.
qed.

realize SubF.Sub.insubN.
proof.
by move=> x; rewrite /p_ /insub_ /= negb_and; case=> ->.
qed.

realize SubF.Sub.insubT.
proof.
move=> x; rewrite /p_ /val_ /insub_ /(\o) /= => -[] p2 p1; rewrite p2 p1 /=.
rewrite /Ext1.SubFF.SubF.Sub.val Ext1.SubFF.SubF.Sub.val_insubd.
move: p1; rewrite /Ext1.SubFF.SubF.p => -> /=.
rewrite /Ext2.SubFF.SubF.Sub.val Ext2.SubFF.SubF.Sub.val_insubd.
move: p2; rewrite /Ext2.SubFF.SubF.p => -> /=.
by apply/SubFFExt2.SubF.Sub.valKd.
qed.

realize SubF.Sub.valP.
proof.
move=> x; rewrite /p_ /val_ /(\o) /=.
rewrite SubFFExt2.SubF.Sub.val_insubd.
rewrite /Ext2.SubFF.SubF.Sub.val.
rewrite -/Ext2.SubFStr.FStr.iter_frobenius_fixed.
(*TODO: all these last admits are straightforward once the FieldStructure clones in Ext1, Ext2 ans SubFF are matched.*)
(*
print Ext2.SubFStr.eq_iter_frobenius_fixed.
*)
admit.
qed.

realize SubF.Sub.valK.
proof.
move=> x; rewrite /val_ /insub_ /(\o) /=.
admit.
qed.

realize SubF.Sub.insubW.
proof.
rewrite /insub_ /wsT_ /(\o) /=.
admit.
qed.

lemma eqn : FFexistence.n = FFexistence.SubFF.n.
proof.
move: Ext1.SubFF.eq_card_pow_n Ext2.SubFF.eq_card_pow_n SubFFExt2.eq_card_pow_n.
(*
print Ext1.SFF.FFStr.FF.FinType.card.
search _  Ext2.SFF.SFT.card.
search _ FFexistence.SubFF.n.
*)
admit.
qed.
*)
end FFexistence.

