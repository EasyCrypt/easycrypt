(* -------------------------------------------------------------------- *)
require import AllCore List Ring Int IntDiv Characteristic Bigalg.
require (*--*) Subtype.
(*---*) import StdOrder.IntOrder.

(* -------------------------------------------------------------------- *)
theory ZModPred.
  type t.

  clone import ZModule with type t <= t.

  inductive zmodpred (p : t -> bool) =
  | ZModPred of
        (p zeror)
      & (forall x, p x => p (-x))
      & (forall x y, p x => p y => p (x + y)).

  lemma zmod0 p : zmodpred p => p zeror.
  proof. by case. qed.

  lemma zmodN p x : zmodpred p => p x => p (-x).
  proof. by case=> _ + _; apply. qed.

  lemma zmodD p x y : zmodpred p => p x => p y => p (x + y).
  proof. by case=> _ _; apply. qed.
  
  lemma zmodB p x y : zmodpred p => p x => p y => p (x - y).
  proof. by move=> zmodp px py; apply/zmodD/zmodN. qed.
end ZModPred.

(* -------------------------------------------------------------------- *)
theory ComRingPred.
  type t.

  clone import ComRing with type t <= t.

  clone import ZModPred with
    type t <= t, theory ZModule <- ComRing.

  inductive ringpred (p : t -> bool) =
  | RingPred of
        (zmodpred p)
      & (p oner)
      & (forall x y, p x => p y => p (x * y))
      & (forall x, p x => p (invr x)).

  lemma ringpred_zmod p : ringpred p => zmodpred p.
  proof. by case. qed.

  hint exact : ringpred_zmod.

  lemma ring0 p : ringpred p => p zeror.
  proof. by move/ringpred_zmod; exact: zmod0. qed.

  lemma ringN p x : ringpred p => p x => p (-x).
  proof. by move/ringpred_zmod; exact: zmodN. qed.

  lemma ringD p x y : ringpred p => p x => p y => p (x + y).
  proof. by move/ringpred_zmod; exact: zmodD. qed.
  
  lemma ringB p x y : ringpred p => p x => p y => p (x - y).
  proof. by move/ringpred_zmod; exact: zmodB. qed.

  lemma ring1 p : ringpred p => p oner.
  proof. by case. qed.
  
 lemma ringM p x y : ringpred p => p x => p y => p (x * y).
  proof. by case=> _ _ + _; apply. qed.

  lemma ringV p x : ringpred p => p x => p (invr x).
  proof. by case=> _ _ _; apply. qed.
end ComRingPred.

(* -------------------------------------------------------------------- *)
abstract theory SubZModule.
  type t, st.

  clone import ZModule as ZMod with type t <= t.
  clone import ZModPred with type t <= t, theory ZModule <- ZMod.

  op p : t -> bool.

  axiom zmodp : zmodpred p.

  hint exact : zmodp.

  clone import Subtype as Sub with
    type T  <- t ,
    type sT <- st,
    pred P  <- p .

  op zeror   = Sub.insubd zeror.
  op (+) x y = Sub.insubd (Sub.val x + Sub.val y).
  op ([-]) x = Sub.insubd (- Sub.val x).

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
  move=> x y; apply/Sub.val_inj.
  by rewrite !Sub.val_insubd !zmodD ?Sub.valP //= addrC.
  qed.

  realize add0r.
  proof.
  move=> x; rewrite /zeror; apply/val_inj.
  by rewrite !val_insubd zmodD ?Sub.valP //= !zmod0 // ?add0r.
  qed.

  realize addNr.
  proof.
  move=> x; rewrite /zeror /SZMod.([-]); apply/val_inj.
  rewrite !val_insubd !(zmodD, zmodN, zmod0) ?Sub.valP  //=.
  + by apply/zmodN/Sub.valP.
  + by apply/addNr.
  qed.
end SubZModule.

(* -------------------------------------------------------------------- *)
abstract theory SubComRing.
  type t, st.

  clone import ComRing as CR with type t <= t.
  clone import ComRingPred with type t <= t, theory ComRing <- CR.

  import ComRingPred.ZModPred.

  op p : t -> bool.

  axiom ringp : ringpred p.

  hint exact : ringp.

  clone include SubZModule with
    type t  <- t ,
    type st <- st,
    op    p <- p ,

    theory ZMod     <- CR,
    theory ZModPred <- ComRingPred.ZModPred

    proof zmodp.

  realize zmodp. by apply/ringpred_zmod. qed.

  clear [SZMod.* SZMod.AddMonoid.*].

  op oner      = Sub.insubd oner.
  op ( * ) x y = Sub.insubd (Sub.val x * Sub.val y).
  op invr x    = Sub.insubd (invr (Sub.val x)).
  pred unit x  = unit (Sub.val x).

  import Sub.

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
  apply/negP; rewrite /zeror /oner; move/(congr1 Sub.val).
  by rewrite !val_insubd !(ring0, ring1) // CR.oner_neq0.
  qed.

  realize mulrA.
  proof.
  move=> x y z; rewrite /( * ) !val_insubd.
  by rewrite !ringM ?valP //= CR.mulrA.
  qed.

  realize mulrC.
  proof.
  move=> x y; apply/val_inj; rewrite !val_insubd.
  by rewrite !ringM ?valP //= CR.mulrC.
  qed.

  realize mul1r.
  proof.
  move=> x; rewrite /oner; apply/val_inj.
  by rewrite !val_insubd ringM ?Sub.valP //= !ring1 //= CR.mul1r.
  qed.

  realize mulrDl.
  proof.
  move=> x y z; rewrite /(+) /( * ) !val_insubd.
  by rewrite !(ringD, ringM) ?valP //= CR.mulrDl.
  qed.

  realize mulVr.
  proof.
  move=> x unit_x; rewrite /( * ) /invr /oner.
  by rewrite val_insubd ringV ?Sub.valP //= mulVr.
  qed.

  realize unitP.
  proof.
  move=> x y; rewrite /( * ) /oner /unit; move/(congr1 Sub.val).
  by rewrite !val_insubd ringM ?valP //= ring1 //; apply/unitP.
  qed.

  realize unitout.
  proof.
  move=> x; rewrite /unit /invr -{3}(valKd x).
  by move=> hnu; apply/congr1/unitout.
  qed.
end SubComRing.

(*
abstract theory SubIDomain.
  clone import IDomain as ID.

  clone include SubComRing with
    theory CR <- ID.

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
    move => x y; rewrite /( * ) /zeror -{2}(Sub.valKd x) -{2}(Sub.valKd y); split.
    + move/(congr1 Sub.val); rewrite !Sub.val_insubd sub_0 sub_mul ?Sub.valP //=.
      by case/mulf_eq0 => ->; [left|right].
    by case => /(congr1 Sub.val); rewrite !Sub.val_insubd Sub.valP sub_0 /= => eq_;
    apply/congr1/mulf_eq0; [left|right].
  qed.

end SubIDomain.


abstract theory SubField.

  clone import Field as F.

  clone include SubIDomain with
    theory ID <- F.

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
    move => x; rewrite /zeror => neq_x; apply/SID.mulVr; rewrite /unit; move: (Sub.val_insubd F.zeror).
    by rewrite sub_0 /= => <-; apply/negP => /Sub.val_inj.
  qed.

  realize unitP.
  proof.
    move => x y /SID.unitP; rewrite /unit /zeror; move: (Sub.val_insubd F.zeror).
    by rewrite sub_0 /= => {1}<-; rewrite implybNN => ->.
  qed.

  realize unitout.
  proof. by move => x /= ->>; apply/SID.unitout; rewrite /unit /zeror /= !Sub.val_insubd sub_0. qed.

end SubField.


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


abstract theory UZMod_IDomain.

  clone import IDomain as ID.

  clone include UZMod_ComRing with
    theory CR <- ID.

end UZMod_IDomain.


abstract theory UZMod_Field.

  clone import Field as F.

  clone include UZMod_IDomain with
    theory ID <- F.

end UZMod_Field.
*)
