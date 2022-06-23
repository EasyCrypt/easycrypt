(* -------------------------------------------------------------------- *)
require import AllCore List Ring Int IntDiv Bigalg.
require (*--*) Subtype.
(*---*) import StdOrder.IntOrder.

(* -------------------------------------------------------------------- *)
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
end ZModulePred.

(* -------------------------------------------------------------------- *)
theory ComRingPred.
  type t.

  clone import ComRing as CR with
    type t <= t.

  clone import ZModulePred with
    type t      <= t,
    theory ZMod <- CR.

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

  lemma comring1 p : comringpred p => p oner.
  proof. by case. qed.
  
 lemma comringM p x y : comringpred p => p x => p y => p (x * y).
  proof. by case=> _ _ + _; apply. qed.

  lemma comringV p x : comringpred p => p x => p (invr x).
  proof. by case=> _ _ _; apply. qed.
end ComRingPred.

(* -------------------------------------------------------------------- *)
theory IDomainPred.
  type t.

  clone import IDomain as ID with
    type t <= t.

  clone import ComRingPred with
    type t    <= t,
    theory CR <- ID.

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

  lemma idomain1 p : idomainpred p => p oner.
  proof. by move/idomainpred_comring; exact: comring1. qed.
  
 lemma idomainM p x y : idomainpred p => p x => p y => p (x * y).
  proof. by move/idomainpred_comring; exact: comringM. qed.

  lemma idomainV p x : idomainpred p => p x => p (invr x).
  proof. by move/idomainpred_comring; exact: comringV. qed.
end IDomainPred.

(* -------------------------------------------------------------------- *)
theory FieldPred.
  type t.

  clone import Field as F with
    type t <= t.

  clone import IDomainPred with
    type t    <= t,
    theory ID <- F.

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

  lemma field1 p : fieldpred p => p oner.
  proof. by move/fieldpred_idomain; exact: idomain1. qed.
  
 lemma fieldM p x y : fieldpred p => p x => p y => p (x * y).
  proof. by move/fieldpred_idomain; exact: idomainM. qed.

  lemma fieldV p x : fieldpred p => p x => p (invr x).
  proof. by move/fieldpred_idomain; exact: idomainV. qed.
end FieldPred.


(* ==================================================================== *)
abstract theory SubZModule.
  type t, st.

  clone import ZModule as ZMod with
    type t <= t.

  clone import ZModulePred with
    type t      <= t,
    theory ZMod <- ZMod.

  op p : t -> bool.

  axiom zmodulep : zmodulepred p.

  hint exact : zmodulep.

  clone import Subtype as Sub with
    type T  <= t ,
    type sT <= st,
    pred P  <- p.

  op zeror   = insubd zeror.
  op (+) x y = insubd (val x + val y).
  op ([-]) x = insubd (- val x).

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
end SubZModule.

(* -------------------------------------------------------------------- *)
abstract theory SubComRing.
  type t, st.

  clone import ComRing as CR with
    type t <= t.

  clone import ComRingPred with
    type t    <= t,
    theory CR <- CR.

  import ComRingPred.ZModulePred.

  op p : t -> bool.

  axiom comringp : comringpred p.

  hint exact : comringp.

  clone include SubZModule with
    type t  <- t ,
    type st <- st,
    op    p <- p ,

    theory ZMod        <- CR,
    theory ZModulePred <- ComRingPred.ZModulePred

    proof zmodulep.

  realize zmodulep. by apply/comringpred_zmodule. qed.

  clear [SZMod.* SZMod.AddMonoid.*].

  import Sub.

  op oner      = insubd oner.
  op ( * ) x y = insubd (val x * val y).
  op invr x    = insubd (invr (val x)).
  pred unit x  = unit (val x).

  lemma val1 : val oner = CR.oner.
  proof. by rewrite /oner val_insubd comring1. qed.

  lemma valM x y : val (x * y) = val x * val y.
  proof. by rewrite /( * ) val_insubd comringM // valP. qed.

  lemma valV x : val (invr x) = invr (val x).
  proof. by rewrite /invr val_insubd comringV // valP. qed.

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
  proof. by move=> x unit_x; apply/val_inj; rewrite valM valV val1 mulVr. qed.

  realize unitP.
  proof. by move=> x y eq_1; rewrite /unit; apply/(unitP _ (val y)); rewrite -valM -val1 eq_1. qed.

  realize unitout.
  proof. by move => x ?; apply/val_inj; rewrite valV unitout. qed.
end SubComRing.

(* -------------------------------------------------------------------- *)
abstract theory SubIDomain.
  type t, st.

  clone import IDomain as ID with
    type t <= t.

  clone import IDomainPred with
    type t    <= t,
    theory ID <- ID.

  import IDomainPred.ComRingPred.

  op p : t -> bool.

  axiom idomainp : idomainpred p.

  hint exact : idomainp.

  clone include SubComRing with
    type t  <- t ,
    type st <- st,
    op    p <- p ,

    theory CR          <- ID,
    theory ComRingPred <- IDomainPred.ComRingPred

    proof comringp.

  realize comringp. by apply/idomainpred_comring. qed.

  clear [SCR.* SCR.AddMonoid.* SCR.MulMonoid.*].

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

  clone import FieldPred with
    type t   <= t,
    theory F <- F.

  import FieldPred.IDomainPred.

  op p : t -> bool.

  axiom fieldp : fieldpred p.

  hint exact : fieldp.

  clone include SubIDomain with
    type t  <- t ,
    type st <- st,
    op    p <- p ,

    theory ID          <- F,
    theory IDomainPred <- FieldPred.IDomainPred

    proof idomainp.

  realize idomainp. by apply/fieldpred_idomain. qed.

  clear [SID.* SID.AddMonoid.* SID.MulMonoid.*].

  import Sub.

  clone import Field as SF with
    type t    <= st,
    op zeror  <= zeror,
    op (+)    <= (+),
    op [-]    <= ([-]),
    op oner   <= oner,
    op ( * )  <= ( * ),
    op invr   <= invr
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
  realize mulf_eq0  by exact SID.mulf_eq0.

  realize mulVr.
  proof. by move => x ?; apply/SID.mulVr; rewrite /unit -val0; apply/negP => /val_inj. qed.

  realize unitP.
  proof. by move => x y /SID.unitP; rewrite /unit -val0; apply/contra => ->. qed.

  realize unitout.
  proof. by move => x /= ->>; apply/SID.unitout; rewrite /unit val0. qed.
end SubField.


(* ==================================================================== *)
abstract theory UZMod_ComRing.
  type t, uz.

  clone import ComRing as CR with
    type t <= t.

  clone import Subtype as Sub with
    type T  <= t,
    type sT <= uz,
    pred P  <- CR.unit.

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
    type t    <- uz,
    op zeror  <- oner,
    op (+)    <- ( * ),
    op [-]  <- invr
    proof *.

  realize addrA.
  proof. by move => x y z; apply/val_inj; rewrite !valM mulrA. qed.

  realize addrC.
  proof. by move => x y; apply/val_inj; rewrite !valM mulrC. qed.

  realize add0r.
  proof. by move => x; apply/val_inj; rewrite valM val1 mul1r. qed.

  realize addNr.
  proof. by move => x; apply/val_inj; rewrite valM valV val1 mulVr // valP. qed.
end UZMod_ComRing.

(* -------------------------------------------------------------------- *)
abstract theory UZMod_IDomain.
  type t, uz.

  clone import IDomain as ID with
    type t <= t.

  clone include UZMod_ComRing with
    type t    <- t,
    type uz   <- uz,
    theory CR <- ID.
end UZMod_IDomain.

(* -------------------------------------------------------------------- *)
abstract theory UZMod_Field.
  type t, uz.

  clone import Field as F with
    type t <= t.

  clone include UZMod_IDomain with
    type t    <- t,
    type uz   <- uz,
    theory ID <- F.
end UZMod_Field.
