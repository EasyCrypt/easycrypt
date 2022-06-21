(* -------------------------------------------------------------------- *)
require import AllCore List Ring Int IntDiv Characteristic Bigalg.
require (*--*) Subtype.
(*---*) import StdOrder.IntOrder.

(* -------------------------------------------------------------------- *)
theory ZModPred.
  type t.

  clone import ZModule as ZMod with type t <= t.

  inductive zmodpred (p : t -> bool) =
  | ZModPred of
        (p zeror)
      & (forall x, p x => p (-x))
      & (forall x y, p x => p y => p (x + y)).

  lemma zmod0 p : zmodpred p => p zeror.
  proof. by case. qed.

  lemma zmodD p x y : zmodpred p => p x => p y => p (x + y).
  proof. by case=> _ _; apply. qed.

  lemma zmodN p x : zmodpred p => p x => p (-x).
  proof. by case=> _ + _; apply. qed.
  
  lemma zmodB p x y : zmodpred p => p x => p y => p (x - y).
  proof. by move=> zmodp px py; apply/zmodD/zmodN. qed.
end ZModPred.

(* -------------------------------------------------------------------- *)
theory ComRingPred.
  type t.

  clone import ComRing as CR with type t <= t.

  clone import ZModPred with
    type t <= t, theory ZMod <- CR.

  inductive comringpred (p : t -> bool) =
  | ComRingPred of
        (zmodpred p)
      & (p oner)
      & (forall x y, p x => p y => p (x * y))
      & (forall x, p x => p (invr x)).

  lemma comringpred_zmod p : comringpred p => zmodpred p.
  proof. by case. qed.

  hint exact : comringpred_zmod.

  lemma comring0 p : comringpred p => p zeror.
  proof. by move/comringpred_zmod; exact: zmod0. qed.

  lemma comringD p x y : comringpred p => p x => p y => p (x + y).
  proof. by move/comringpred_zmod; exact: zmodD. qed.

  lemma comringN p x : comringpred p => p x => p (-x).
  proof. by move/comringpred_zmod; exact: zmodN. qed.
  
  lemma comringB p x y : comringpred p => p x => p y => p (x - y).
  proof. by move/comringpred_zmod; exact: zmodB. qed.

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

  clone import IDomain as ID with type t <= t.

  clone import ComRingPred with
    type t <= t, theory CR <- ID.

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

  clone import Field as F with type t <= t.

  clone import IDomainPred with
    type t <= t, theory ID <- F.

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

  clone import ZModule as ZMod with type t <= t.
  clone import ZModPred with type t <= t, theory ZMod <- ZMod.

  op p : t -> bool.

  axiom zmodp : zmodpred p.

  hint exact : zmodp.

  clone import Subtype as Sub with
    type T  <- t ,
    type sT <- st,
    pred P  <- p .

  op zeror   = insubd zeror.
  op (+) x y = insubd (val x + val y).
  op ([-]) x = insubd (- val x).

  clone import ZModule as SZMod with
    type t    <= st,
    op zeror  <= zeror,
    op (+)    <= (+),
    op [-]    <= ([-])
    proof *.

  realize addrA.
  proof.
  by move=> x y z; rewrite /(+) !val_insubd !zmodD ?valP //= addrA.
  qed.

  realize addrC.
  proof.
  move=> x y; apply/val_inj.
  by rewrite !val_insubd !zmodD ?valP //= addrC.
  qed.

  realize add0r.
  proof.
  move=> x; rewrite /zeror; apply/val_inj.
  by rewrite !val_insubd zmodD ?valP //= !zmod0 // ?add0r.
  qed.

  realize addNr.
  proof.
  move=> x; rewrite /zeror /SZMod.([-]); apply/val_inj.
  rewrite !val_insubd !(zmodD, zmodN, zmod0) ?valP  //=.
  + by apply/zmodN/valP.
  + by apply/addNr.
  qed.
end SubZModule.

(* -------------------------------------------------------------------- *)
abstract theory SubComRing.
  type t, st.

  clone import ComRing as CR with type t <= t.
  clone import ComRingPred with type t <= t, theory CR <- CR.

  import ComRingPred.ZModPred.

  op p : t -> bool.

  axiom comringp : comringpred p.

  hint exact : comringp.

  clone include SubZModule with
    type t  <- t ,
    type st <- st,
    op    p <- p ,

    theory ZMod     <- CR,
    theory ZModPred <- ComRingPred.ZModPred

    proof zmodp.

  realize zmodp. by apply/comringpred_zmod. qed.

  clear [SZMod.* SZMod.AddMonoid.*].

  import Sub.

  op oner      = insubd oner.
  op ( * ) x y = insubd (val x * val y).
  op invr x    = insubd (invr (val x)).
  pred unit x  = unit (val x).

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
  proof.
  move=> x y z; rewrite /( * ) !val_insubd.
  by rewrite !comringM ?valP //= mulrA.
  qed.

  realize mulrC.
  proof.
  move=> x y; apply/val_inj; rewrite !val_insubd.
  by rewrite !comringM ?valP //= mulrC.
  qed.

  realize mul1r.
  proof.
  move=> x; rewrite /oner; apply/val_inj.
  by rewrite !val_insubd comringM ?valP //= !comring1 //= mul1r.
  qed.

  realize mulrDl.
  proof.
  move=> x y z; rewrite /(+) /( * ) !val_insubd.
  by rewrite !(comringD, comringM) ?valP //= mulrDl.
  qed.

  realize mulVr.
  proof.
  move=> x unit_x; rewrite /( * ) /invr /oner.
  by rewrite val_insubd comringV ?valP //= mulVr.
  qed.

  realize unitP.
  proof.
  move=> x y; rewrite /( * ) /oner /unit; move/(congr1 val).
  by rewrite !val_insubd comringM ?valP //= comring1 //; apply/unitP.
  qed.

  realize unitout.
  proof.
  move=> x; rewrite /unit /invr -{3}(valKd x).
  by move=> ?; apply/congr1/unitout.
  qed.
end SubComRing.

(* -------------------------------------------------------------------- *)
abstract theory SubIDomain.
  type t, st.

  clone import IDomain as ID with type t <= t.
  clone import IDomainPred with type t <= t, theory ID <- ID.

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
    move => x y; rewrite /( * ) /zeror -{2}(valKd x) -{2}(valKd y); split.
    + move/(congr1 Sub.val); rewrite !val_insubd idomain0 // idomainM ?valP //=.
      by case/mulf_eq0 => ->; [left|right].
    by case => /(congr1 val); rewrite !val_insubd valP idomain0 //= => eq_;
    apply/congr1/mulf_eq0; [left|right].
  qed.

end SubIDomain.

(* -------------------------------------------------------------------- *)
abstract theory SubField.
  type t, st.

  clone import Field as F with type t <= t.
  clone import FieldPred with type t <= t, theory F <- F.

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
  proof.
    move => x; rewrite /zeror => neq_x; apply/SID.mulVr; rewrite /unit; move: (val_insubd F.zeror).
    by rewrite field0 //= => <-; apply/negP => /val_inj.
  qed.

  realize unitP.
  proof.
    move => x y /SID.unitP; rewrite /unit /zeror; move: (val_insubd F.zeror).
    by rewrite field0 //= => {1}<-; rewrite implybNN => ->.
  qed.

  realize unitout.
  proof. by move => x /= ->>; apply/SID.unitout; rewrite /unit /zeror /= !val_insubd field0. qed.

end SubField.


(* ==================================================================== *)
abstract theory UZMod_ComRing.

  clone import ComRing as CR.

  type uz.

  clone Subtype as Sub with
    type T <- CR.t,
    type sT <- uz,
    pred P <- CR.unit.

  op oner = Sub.insubd oner.
  op ( * ) x y = Sub.insubd (Sub.val x * Sub.val y).
  op invr x = Sub.insubd (invr (Sub.val x)).

  clone import ZModule as UZMod with
    type t    <- uz,
    op zeror  <- oner,
    op (+)    <- ( * ),
    op [-]  <- invr
    proof *.

  realize addrA.
  proof. by move => x y z; rewrite /( * ) !Sub.val_insubd !unitrM !Sub.valP /=; rewrite mulrA. qed.

  realize addrC.
  proof.
    move => x y; apply/Sub.val_inj.
    by rewrite !Sub.val_insubd !unitrM !Sub.valP /= mulrC.
  qed.

  realize add0r.
  proof.
    move => x; rewrite /zeror; apply/Sub.val_inj.
    by rewrite !Sub.val_insubd !unitrM !Sub.valP unitr1 /= unitr1 /= mul1r.
  qed.

  realize addNr.
  proof.
    move => x; rewrite /oner /invr; apply/Sub.val_inj.
    rewrite !Sub.val_insubd unitrM unitrV !Sub.valP unitr1 /= unitrV Sub.valP /=.
    by apply/mulVr/Sub.valP.
  qed.

end UZMod_ComRing.

(* -------------------------------------------------------------------- *)
abstract theory UZMod_IDomain.

  clone import IDomain as ID.

  clone include UZMod_ComRing with
    theory CR <- ID.

end UZMod_IDomain.

(* -------------------------------------------------------------------- *)
abstract theory UZMod_Field.

  clone import Field as F.

  clone include UZMod_IDomain with
    theory ID <- F.

end UZMod_Field.
