(* -------------------------------------------------------------------- *)
require import AllCore List Ring Int IntDiv Bigalg RingStruct.
require (*--*) Subtype.
(*---*) import StdOrder.IntOrder.


(* ==================================================================== *)
theory ZModulePred.
  type t.

  clone import ZModule as ZMod with
    type t <= t.

  inductive zmodulepred (p : t -> bool) =
  | ZModulePred of
        (p zeror)
      & (forall x, p x => p (-x))
      & (forall x y, p x => p y => p (x + y)).

  lemma zmodule0 p : zmodulepred p => p zeror.
  proof. by case. qed.

  lemma zmoduleD p x y : zmodulepred p => p x => p y => p (x + y).
  proof. by case=> _ _; apply. qed.

  lemma zmoduleN p x : zmodulepred p => p x => p (-x).
  proof. by case=> _ + _; apply. qed.
  
  lemma zmoduleB p x y : zmodulepred p => p x => p y => p (x - y).
  proof. by move=> zmodulep px py; apply/zmoduleD/zmoduleN. qed.

  lemma zmoduleMz p x n : zmodulepred p => p x => p (intmul x n).
  proof.
    move=> zmodulep; wlog: n / 0 <= n => [wlogn|].
    + case (0 <= n) => [|/ltrNge/ltzW/ler_opp2/=] /wlogn // + px.
      move/(_ px); rewrite ZMod.mulrNz=> /(zmoduleN p _ zmodulep).
      by rewrite opprK.
    elim: n => [|n le0n IHn]; [by rewrite ZMod.mulr0z zmodule0|].
    by rewrite ZMod.mulrSz => px; move/(_ px): IHn => p_; apply/zmoduleD.
  qed.
end ZModulePred.

(* -------------------------------------------------------------------- *)
theory ComRingPred.
  type t.

  clone import ComRing as CR with
    type t <= t.

  clone include ZModulePred with
    type t      <- t,
    theory ZMod <= CR.

  inductive comringpred (p : t -> bool) =
  | ComRingPred of
        (zmodulepred p)
      & (p oner)
      & (forall x y, p x => p y => p (x * y))
      & (forall x, p x => p (invr x)).

  lemma comringpred_zmodule p : comringpred p => zmodulepred p.
  proof. by case. qed.

  hint exact : comringpred_zmodule.

  lemma comring0 p : comringpred p => p zeror.
  proof. by move/comringpred_zmodule; exact: zmodule0. qed.

  lemma comringD p x y : comringpred p => p x => p y => p (x + y).
  proof. by move/comringpred_zmodule; exact: zmoduleD. qed.

  lemma comringN p x : comringpred p => p x => p (-x).
  proof. by move/comringpred_zmodule; exact: zmoduleN. qed.
  
  lemma comringB p x y : comringpred p => p x => p y => p (x - y).
  proof. by move/comringpred_zmodule; exact: zmoduleB. qed.

  lemma comringMz p x n : comringpred p => p x => p (intmul x n).
  proof. by move/comringpred_zmodule; exact: zmoduleMz. qed.

  lemma comring1 p : comringpred p => p oner.
  proof. by case. qed.
  
 lemma comringM p x y : comringpred p => p x => p y => p (x * y).
  proof. by case=> _ _ + _; apply. qed.

  lemma comringV p x : comringpred p => p x => p (invr x).
  proof. by case=> _ _ _; apply. qed.

  lemma comringX p x n : comringpred p => p x => p (exp x n).
  proof.
    move=> comringp; wlog: n / 0 <= n => [wlogn|].
    + case (0 <= n) => [|/ltrNge/ltzW/ler_opp2/=] /wlogn // + px.
      move/(_ px); rewrite exprN => /(comringV _ _ comringp).
      by rewrite invrK.
    elim: n => [|n le0n IHn]; [by rewrite CR.expr0 comring1|].
    by rewrite CR.exprS // => px; move/(_ px): IHn => p_; apply/comringM.
  qed.
end ComRingPred.

(* -------------------------------------------------------------------- *)
theory IDomainPred.
  type t.

  clone import IDomain as ID with
    type t <= t.

  clone include ComRingPred with
    type t    <- t,
    theory ZMod <= ID,
    theory CR <= ID.

  inductive idomainpred (p : t -> bool) =
  | IDomainPred of
        (comringpred p).

  lemma idomainpred_comring p : idomainpred p => comringpred p.
  proof. by case. qed.

  hint exact : idomainpred_comring.

  lemma idomain0 p : idomainpred p => p zeror.
  proof. by move/idomainpred_comring; exact: comring0. qed.

  lemma idomainD p x y : idomainpred p => p x => p y => p (x + y).
  proof. by move/idomainpred_comring; exact: comringD. qed.

  lemma idomainN p x : idomainpred p => p x => p (-x).
  proof. by move/idomainpred_comring; exact: comringN. qed.
  
  lemma idomainB p x y : idomainpred p => p x => p y => p (x - y).
  proof. by move/idomainpred_comring; exact: comringB. qed.

  lemma idomainMz p x n : idomainpred p => p x => p (intmul x n).
  proof. by move/idomainpred_comring; exact: comringMz. qed.

  lemma idomain1 p : idomainpred p => p oner.
  proof. by move/idomainpred_comring; exact: comring1. qed.
  
 lemma idomainM p x y : idomainpred p => p x => p y => p (x * y).
  proof. by move/idomainpred_comring; exact: comringM. qed.

  lemma idomainV p x : idomainpred p => p x => p (invr x).
  proof. by move/idomainpred_comring; exact: comringV. qed.

  lemma idomainX p x n : idomainpred p => p x => p (exp x n).
  proof. by move/idomainpred_comring; exact: comringX. qed.
end IDomainPred.

(* -------------------------------------------------------------------- *)
theory FieldPred.
  type t.

  clone import Field as F with
    type t <= t.

  clone include IDomainPred with
    type t    <- t,
    theory ZMod <= F,
    theory CR <= F,
    theory ID <= F.

  inductive fieldpred (p : t -> bool) =
  | FieldPred of
        (idomainpred p).

  lemma fieldpred_idomain p : fieldpred p => idomainpred p.
  proof. by case. qed.

  hint exact : fieldpred_idomain.

  lemma field0 p : fieldpred p => p zeror.
  proof. by move/fieldpred_idomain; exact: idomain0. qed.

  lemma fieldD p x y : fieldpred p => p x => p y => p (x + y).
  proof. by move/fieldpred_idomain; exact: idomainD. qed.

  lemma fieldidomainN p x : fieldpred p => p x => p (-x).
  proof. by move/fieldpred_idomain; exact: idomainN. qed.
  
  lemma fieldB p x y : fieldpred p => p x => p y => p (x - y).
  proof. by move/fieldpred_idomain; exact: idomainB. qed.

  lemma fieldMz p x n : fieldpred p => p x => p (intmul x n).
  proof. by move/fieldpred_idomain; exact: idomainMz. qed.

  lemma field1 p : fieldpred p => p oner.
  proof. by move/fieldpred_idomain; exact: idomain1. qed.
  
 lemma fieldM p x y : fieldpred p => p x => p y => p (x * y).
  proof. by move/fieldpred_idomain; exact: idomainM. qed.

  lemma fieldV p x : fieldpred p => p x => p (invr x).
  proof. by move/fieldpred_idomain; exact: idomainV. qed.

  lemma fieldX p x n : fieldpred p => p x => p (exp x n).
  proof. by move/fieldpred_idomain; exact: idomainX. qed.
end FieldPred.


(* ==================================================================== *)
abstract theory SubZModule.
  type t, st.

  clone import ZModule as ZMod with
    type t <= t.

  clone import ZModulePred as ZModPr with
    type t      <= t,
    theory ZMod <= ZMod.

  op p : t -> bool.

  axiom zmodulep : zmodulepred p.

  hint exact : zmodulep.

  clone import Subtype as Sub with
    type T  <= t ,
    type sT <= st,
    pred P  <= p.

  op zeror   = insubd zeror.
  op (+) x y = insubd (val x + val y).
  op ([-]) x = insubd (- val x).

  lemma insubd0 : insubd ZMod.zeror = zeror.
  proof. by rewrite /zeror. qed.

  lemma insubdD x y : p x => p y => insubd (x + y) = insubd x + insubd y.
  proof.
    move=> px py; rewrite /insubd; move: (insubT _ px) (insubT _ py).
    by case: (insub x) => // ox /= <<-; case: (insub y) => // oy /= <<-.
  qed.

  lemma insubdN x : p x => insubd (-x) = - insubd x.
  proof.
    move=> px; rewrite /insubd; move: (insubT _ px).
    by case: (insub x) => // ox /= <<-.
  qed.

  lemma val0 : val zeror = ZMod.zeror.
  proof. by rewrite /zeror val_insubd zmodule0. qed.

  lemma valD x y : val (x + y) = val x + val y.
  proof. by rewrite /(+) val_insubd zmoduleD // valP. qed.

  lemma valN x : val (-x) = - val x.
  proof. by rewrite /(-) val_insubd zmoduleN // valP. qed.

  clone import ZModule as SZMod with
    type t    <= st,
    op zeror  <= zeror,
    op (+)    <= (+),
    op [-]    <= ([-])
    proof *.

  realize addrA.
  proof. by move=> x y z; apply/val_inj; rewrite !valD addrA. qed.

  realize addrC.
  proof. by move=> x y; apply/val_inj; rewrite !valD addrC. qed.

  realize add0r.
  proof. by move=> x; apply/val_inj; rewrite valD val0 add0r. qed.

  realize addNr.
  proof. by move=> x; apply/val_inj; rewrite valD valN val0 addNr. qed.

  lemma insubdB x y : p x => p y => insubd (x - y) = insubd x - insubd y.
  proof.
    move=> px py; rewrite insubdD //; [by apply/zmoduleN|].
    by rewrite insubdN.
  qed.

  lemma insubdMz x n : p x => insubd (intmul x n) = intmul (insubd x) n.
  proof.
    wlog: n / 0 <= n => [wlogn|].
    + case (0 <= n) => [|/ltrNge/ltzW/ler_opp2/=] /wlogn // + px.
      by move/(_ px); rewrite ZMod.mulrNz SZMod.mulrNz insubdN ?zmoduleMz // => /SZMod.oppr_inj.
    elim: n => [|n le0n IHn]; [by rewrite ZMod.mulr0z SZMod.mulr0z|].
    by rewrite ZMod.mulrSz SZMod.mulrSz => px; rewrite -IHn // insubdD // zmoduleMz.
  qed.

  lemma valB (x y : st) : val (x - y) = val x - val y.
  proof. by rewrite valD valN. qed.

  lemma valMz (x : st) n : val (intmul x n) = intmul (val x) n.
  proof.
    rewrite -valKd -insubdMz ?valP //.
    by rewrite valKd val_insubd zmoduleMz // valP.
  qed.
end SubZModule.

(* -------------------------------------------------------------------- *)
abstract theory SubComRing.
  type t, st.

  clone import ComRing as CR with
    type t <= t.

  clone import ComRingPred as CRPr with
    type t    <= t,
    theory CR <= CR.

  op p : t -> bool.

  axiom comringp : comringpred p.

  hint exact : comringp.

  clone include SubZModule with
    type t  <- t ,
    type st <- st,
    op    p <- p ,
    theory ZMod   <= CR,
    theory ZModPr <= CRPr
    proof zmodulep.

  realize zmodulep. by apply/comringpred_zmodule. qed.

  import Sub.

  op oner      = insubd oner.
  op ( * ) x y = insubd (val x * val y).
  op invr x    = insubd (invr (val x)). print unit.
  pred unit x  = unit (val x).

  lemma val1 : val oner = CR.oner.
  proof. by rewrite /oner val_insubd comring1. qed.

  lemma valM x y : val (x * y) = val x * val y.
  proof. by rewrite /( * ) val_insubd comringM // valP. qed.

  lemma valV x : val (invr x) = invr (val x).
  proof. by rewrite /invr val_insubd comringV // valP. qed.

  lemma insubd1 : insubd CR.oner = oner.
  proof. by rewrite /oner. qed.

  lemma insubdM x y : p x => p y => insubd (x * y) = insubd x * insubd y.
  proof.
    move=> px py; rewrite /insubd; move: (insubT _ px) (insubT _ py).
    by case: (insub x) => // ox /= <<-; case: (insub y) => // oy /= <<-.
  qed.

  lemma insubdV x : p x => insubd (invr x) = invr (insubd x).
  proof.
    move=> px; rewrite /insubd; move: (insubT _ px).
    by case: (insub x) => // ox /= <<-.
  qed.

  clone import ComRing as SCR with
    type t    <= st,
    op zeror  <= zeror,
    op (+)    <= (+),
    op [-]    <= ([-]),
    op oner   <= oner,
    op ( * )  <= ( * ),
    op invr   <= invr,
    op intmul <= SZMod.intmul,
    pred unit <= unit
    proof *.

  realize addrA by exact SZMod.addrA.
  realize addrC by exact SZMod.addrC.
  realize add0r by exact SZMod.add0r.
  realize addNr by exact SZMod.addNr.

  realize oner_neq0.
  proof.
  apply/negP; rewrite /zeror /oner; move/(congr1 val).
  by rewrite !val_insubd !(comring0, comring1) // oner_neq0.
  qed.

  realize mulrA.
  proof. by move=> x y z; apply/val_inj; rewrite !valM mulrA. qed.

  realize mulrC.
  proof. by move=> x y; apply/val_inj; rewrite !valM mulrC. qed.

  realize mul1r.
  proof. by move=> x; apply/val_inj; rewrite valM val1 mul1r. qed.

  realize mulrDl.
  proof. by move=> x y z; apply/val_inj; rewrite valD !valM valD mulrDl. qed.

  realize mulVr.
  proof. by move=> x ?; apply/val_inj; rewrite valM valV val1 mulVr. qed.

  realize unitP.
  proof. by move=> x y /(congr1 val); rewrite valM val1 => /unitP. qed.

  realize unitout.
  proof. by move=> x ?; apply/val_inj; rewrite valV unitout. qed.

  lemma insubdX x n : p x => insubd (exp x n) = exp (insubd x) n.
  proof.
    wlog: n / 0 <= n => [wlogn|].
    + case (0 <= n) => [|/ltrNge/ltzW/ler_opp2/=] /wlogn // + px.
      by move/(_ px); rewrite CR.exprN SCR.exprN insubdV ?comringX // => /SCR.invr_inj.
    elim: n => [|n le0n IHn]; [by rewrite CR.expr0 SCR.expr0|].
    by rewrite CR.exprS // SCR.exprS // => px; rewrite -IHn // insubdM // comringX.
  qed.

  lemma valX (x : st) n : val (exp x n) = exp (val x) n.
  proof.
    rewrite -valKd -insubdX ?valP //.
    by rewrite valKd val_insubd comringX // valP.
  qed.
end SubComRing.

(* -------------------------------------------------------------------- *)
abstract theory SubIDomain.
  type t, st.

  clone import IDomain as ID with
    type t <= t.

  clone import IDomainPred as IDPr with
    type t    <= t,
    theory ID <= ID.

  op p : t -> bool.

  axiom idomainp : idomainpred p.

  hint exact : idomainp.

  clone include SubComRing with
    type t  <- t ,
    type st <- st,
    op    p <- p ,
    theory ZMod <= ID,
    theory CR   <= ID,
    theory ZModPr <= IDPr,
    theory CRPr <= IDPr
    proof comringp.

  realize comringp. by apply/idomainpred_comring. qed.

  import Sub.

  clone import IDomain as SID with
    type t    <= st,
    op zeror  <= zeror,
    op (+)    <= (+),
    op [-]    <= ([-]),
    op oner   <= oner,
    op ( * )  <= ( * ),
    op invr   <= invr,
    pred unit <= unit
    proof *.

  realize addrA     by exact SCR.addrA.
  realize addrC     by exact SCR.addrC.
  realize add0r     by exact SCR.add0r.
  realize addNr     by exact SCR.addNr.
  realize oner_neq0 by exact SCR.oner_neq0.
  realize mulrA     by exact SCR.mulrA.
  realize mulrC     by exact SCR.mulrC.
  realize mul1r     by exact SCR.mul1r.
  realize mulrDl    by exact SCR.mulrDl.
  realize mulVr     by exact SCR.mulVr.
  realize unitP     by exact SCR.unitP.
  realize unitout   by exact SCR.unitout.

  realize mulf_eq0.
  proof.
    move => x y; split => [eq_|[->>|->>]]; last 2 by apply/val_inj; rewrite valM val0 mulf_eq0.
    by move: (mulf_eq0 (val x) (val y)); rewrite -valM eq_ val0 /= -val0; case => ?; [left|right]; apply/val_inj.
  qed.
end SubIDomain.

(* -------------------------------------------------------------------- *)
abstract theory SubField.
  type t, st.

  clone import Field as F with
    type t <= t.

  clone import FieldPred as FPr with
    type t   <= t,
    theory F <= F.

  op p : t -> bool.

  axiom fieldp : fieldpred p.

  hint exact : fieldp.

  clone include SubIDomain with
    type t  <- t ,
    type st <- st,
    op    p <- p ,
    theory ZMod   <= F,
    theory CR   <= F,
    theory ID   <= F,
    theory ZModPr <= FPr,
    theory CRPr <= FPr,
    theory IDPr <= FPr
    proof idomainp.

  realize idomainp. by apply/fieldpred_idomain. qed.

  import Sub.

  clone import Field as SF with
    type t    <= st,
    op zeror  <= zeror,
    op (+)    <= (+),
    op [-]    <= ([-]),
    op oner   <= oner,
    op ( * )  <= ( * ),
    op invr   <= invr,
    pred unit <= unit
    proof *.

  realize addrA     by exact SID.addrA.
  realize addrC     by exact SID.addrC.
  realize add0r     by exact SID.add0r.
  realize addNr     by exact SID.addNr.
  realize oner_neq0 by exact SID.oner_neq0.
  realize mulrA     by exact SID.mulrA.
  realize mulrC     by exact SID.mulrC.
  realize mul1r     by exact SID.mul1r.
  realize mulrDl    by exact SID.mulrDl.
  realize mulVr     by exact SID.mulVr.
  realize unitP     by exact SID.unitP.
  realize unitout   by exact SID.unitout.
  realize mulf_eq0  by exact SID.mulf_eq0.

  realize unitfP.
  proof.
    move => x; apply/contraLR => /= neg_unit; apply/val_inj; rewrite val0.
    by move: neg_unit; apply/contraLR => /= /unitfP.
  qed.
end SubField.


(* ==================================================================== *)
abstract theory UZMod_ComRing.
  type t, uz.

  clone import ComRing as CR with
    type t <= t.

  clone import Subtype as Sub with
    type T  <= t,
    type sT <= uz,
    pred P  <= CR.unit.

  op oner = insubd oner.
  op ( * ) x y = insubd (val x * val y).
  op invr x = insubd (invr (val x)).

  lemma val1 : val oner = CR.oner.
  proof. by rewrite /oner val_insubd unitr1. qed.

  lemma valM x y : val (x * y) = val x * val y.
  proof. by rewrite /( * ) val_insubd unitrM !valP. qed.

  lemma valV x : val (invr x) = invr (val x).
  proof. by rewrite /invr val_insubd unitrV valP. qed.

  clone import ZModule as UZMod with
    type t    <= uz,
    op zeror  <= oner,
    op (+)    <= ( * ),
    op [-]    <= invr
    proof *.

  realize addrA.
  proof. by move => x y z; apply/val_inj; rewrite !valM mulrA. qed.

  realize addrC.
  proof. by move => x y; apply/val_inj; rewrite !valM mulrC. qed.

  realize add0r.
  proof. by move => x; apply/val_inj; rewrite valM val1 mul1r. qed.

  realize addNr.
  proof. by move => x; apply/val_inj; rewrite valM valV val1 mulVr // valP. qed.

  clone import ZModuleStruct as UZModStr with
    type t      <= uz,
    theory ZMod <= UZMod.

  lemma val_intmul_ge0 x n :
    0 <= n =>
    val (UZMod.intmul x n) = exp (val x) n.
  proof.
    elim n => [|n le0n IHn]; [by rewrite mulr0z expr0 val1|].
    by rewrite mulrSz valM IHn exprS.
  qed.
end UZMod_ComRing.

(* -------------------------------------------------------------------- *)
abstract theory UZMod_IDomain.
  type t, uz.

  clone import IDomain as ID with
    type t <= t.

  clone include UZMod_ComRing with
    type t    <- t,
    type uz   <- uz,
    theory CR <= ID.
end UZMod_IDomain.

(* -------------------------------------------------------------------- *)
abstract theory UZMod_Field.
  type t, uz.

  clone import Field as F with
    type t <= t.

  clone include UZMod_IDomain with
    type t    <- t,
    type uz   <- uz,
    theory CR <= F,
    theory ID <= F.

  lemma val_intmul x n :
    Sub.val (UZMod.intmul x n) = exp (Sub.val x) n.
  proof.
    case (0 <= n) => [|/ltrNge/ltzW]; [by apply/val_intmul_ge0|].
    rewrite -(IntID.opprK n) oppr_le0 => le0_.
    by rewrite UZMod.mulrNz valV exprN; congr; apply/val_intmul_ge0.
  qed.
end UZMod_Field.


(* ==================================================================== *)
abstract theory SubZModuleStruct.
  type t, st.

  clone import SubZModule as SubZMod with
    type t <= t,
    type st <= st.

  clone import ZModuleStruct as ZModStr with
    type t <= t,
    theory ZMod <= SubZMod.ZMod.

  clone import ZModuleStruct as SZModStr with
    type t <= st,
    theory ZMod <= SubZMod.SZMod.

  lemma eq_order x : order (SubZMod.Sub.val x) = order x.
  proof.
    rewrite /order; apply/IntMin.eq_argmin => i le0i /=.
    rewrite /idfun /= -valMz -/ZModPr.ZMod.zeror -val0; apply/andb_id2l => lt0i.
    by apply/eq_iff; split=> [|->] //; apply/SubZMod.Sub.val_inj.
  qed.

  lemma eq_orbit x y : orbit (SubZMod.Sub.val x) (SubZMod.Sub.val y) = orbit x y.
  proof.
    apply/eq_iff/exists_eq => n /=; apply/eq_iff.
    by rewrite -valMz; split=> [|->] // /SubZMod.Sub.val_inj.
  qed.

  lemma eq_orbit_list x : orbit_list (SubZMod.Sub.val x) = map SubZMod.Sub.val (orbit_list x).
  proof.
    rewrite map_mkseq -eq_order; apply/eq_in_mkseq.
    by move=> i _ ; rewrite /(\o) /= valMz.
  qed.

  lemma eq_eqv_orbit x y z : eqv_orbit (SubZMod.Sub.val x) (SubZMod.Sub.val y) (SubZMod.Sub.val z) = eqv_orbit x y z.
  proof. by rewrite /eqv_orbit -valB eq_orbit. qed.

end SubZModuleStruct.

(* -------------------------------------------------------------------- *)
abstract theory SubComRingStruct.
  type t, st.

  clone import SubComRing as SubCR with
    type t <= t,
    type st <= st.

  clone import ComRingStruct as CRStr with
    type t <= t,
    theory CR <= SubCR.CR.

  clone import ComRingStruct as SCRStr with
    type t <= st,
    theory CR <= SubCR.SCR.

  clone include SubZModuleStruct with
    type t <- t,
    type st <- st,
    theory SubZMod <= SubCR,
    theory ZModStr <= CRStr,
    theory SZModStr <= SCRStr.

  lemma eq_char : CRStr.char = SCRStr.char.
  proof. by rewrite /char -eq_order val1. qed.

end SubComRingStruct.

(* -------------------------------------------------------------------- *)
abstract theory SubIDomainStruct.
  type t, st.

  clone import SubIDomain as SubID with
    type t <= t,
    type st <= st.

  clone import IDomainStruct as IDStr with
    type t <= t,
    theory ID <= SubID.ID.

  clone import IDomainStruct as SIDStr with
    type t <= st,
    theory ID <= SubID.SID.

  clone include SubComRingStruct with
    type t <- t,
    type st <- st,
    theory SubZMod <= SubID,
    theory SubCR <= SubID,
    theory ZModStr <= IDStr,
    theory CRStr <= IDStr,
    theory SZModStr <= SIDStr,
    theory SCRStr <= SIDStr.

  lemma eq_frobenius x : frobenius (SubZMod.Sub.val x) = SubZMod.Sub.val (frobenius x).
  proof. by rewrite /frobenius -valX eq_char. qed.

  lemma eq_iter_frobenius_fixed n x : iter_frobenius_fixed n (SubZMod.Sub.val x) = iter_frobenius_fixed n x.
  proof.
    rewrite /iter_frobenius_fixed.
    have ->: iter n IDStr.frobenius (SubZMod.Sub.val x) = SubZMod.Sub.val (iter n SIDStr.frobenius x).
    + case (0 <= n) => [|/ltrNge/ltzW len0]; [|by rewrite !iter0].
      by elim: n => [|n le0n IHn]; [rewrite !iter0|rewrite !iterS // IHn eq_frobenius].
    by apply/eq_iff; split=> [|->] //; apply/SubZMod.Sub.val_inj.
  qed.
end SubIDomainStruct.

(* -------------------------------------------------------------------- *)
abstract theory SubFieldStruct.
  type t, st.

  clone import SubField as SubF with
    type t <= t,
    type st <= st.

  clone import FieldStruct as FStr with
    type t <= t,
    theory F <= SubF.F.

  clone import FieldStruct as SFStr with
    type t <= st,
    theory F <= SubF.SF.

  clone include SubIDomainStruct with
    type t <- t,
    type st <- st,
    theory SubZMod <= SubF,
    theory SubCR <= SubF,
    theory SubID <= SubF,
    theory ZModStr <= FStr,
    theory CRStr <= FStr,
    theory IDStr <= FStr,
    theory SZModStr <= SFStr,
    theory SCRStr <= SFStr,
    theory SIDStr <= SFStr.
end SubFieldStruct.

