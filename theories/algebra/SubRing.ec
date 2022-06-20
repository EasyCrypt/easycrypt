require import AllCore List Ring Int IntDiv Characteristic Bigalg.
require (*--*) Subtype.
(*---*) import StdOrder.IntOrder.


abstract theory SubZModule.

  clone import ZModule as ZMod.

  type st.

  op w : ZMod.t.

  (*TODO: issue in FiniteField if this is a pred.*)
  op in_sub : ZMod.t -> bool.

  axiom sub_w : in_sub w.
  axiom sub_add x y : in_sub x => in_sub y => in_sub (x + y).
  axiom sub_opp x : in_sub x => in_sub (-x).

  lemma sub_0 : in_sub zeror.
  proof. by rewrite -(subrr w); apply/sub_add; [apply/sub_w|apply/sub_opp/sub_w]. qed.

  clone Subtype as Sub with
    type T <- ZMod.t,
    type sT <- st,
    pred P <- in_sub.

  op zeror = Sub.insubd zeror.
  op (+) x y = Sub.insubd (Sub.val x + Sub.val y).
  op ([-]) x = Sub.insubd (- Sub.val x).

  clone import ZModule as SZMod with
    type t    <= st,
    op zeror  <= zeror,
    op (+)    <= (+),
    op [-]    <= ([-])
    proof *.

  realize addrA.
  proof. by move => x y z; rewrite /(+) !Sub.val_insubd !sub_add ?Sub.valP //= ZMod.addrA. qed.

  realize addrC.
  proof.
    move => x y; apply/Sub.val_inj.
    by rewrite !Sub.val_insubd !sub_add ?Sub.valP //= ZMod.addrC.
  qed.

  realize add0r.
  proof.
    move => x; rewrite /zeror; apply/Sub.val_inj.
    by rewrite !Sub.val_insubd sub_add ?Sub.valP //= ?sub_0 //= ?sub_0 //= ZMod.add0r.
  qed.

  realize addNr.
  proof.
    move => x; rewrite /zeror /SZMod.([-]); apply/Sub.val_inj.
    rewrite !Sub.val_insubd sub_add ?sub_opp ?Sub.valP ?sub_0 //=.
    + by apply/sub_opp/Sub.valP.
    by apply/ZMod.addNr.
  qed.

end SubZModule.


abstract theory SubComRing.

  clone import ComRing as CR.

  clone include SubZModule with
    theory ZMod <- CR.

  op wu : CR.t.

  axiom unit_wu : unit wu.
  axiom sub_wu : in_sub wu.
  axiom sub_mul x y : in_sub x => in_sub y => in_sub (x * y).
  axiom sub_inv x : in_sub x => in_sub (invr x).

  lemma sub_1 : in_sub oner.
  proof. by rewrite -(mulVr _ unit_wu); apply/sub_mul; [apply/sub_inv/sub_wu|apply/sub_wu]. qed.

  op oner = Sub.insubd oner.
  op ( * ) x y = Sub.insubd (Sub.val x * Sub.val y).
  op invr x = Sub.insubd (invr (Sub.val x)).
  pred unit x = unit (Sub.val x).

  (*TODO: can I do this with a clone with theory?*)
  clone import ComRing as SCR with
    type t    <= st,
    op zeror  <= zeror,
    op (+)    <= (+),
    op [-]    <= ([-]),
    op oner   <= oner,
    op ( * )  <= ( * ),
    op invr   <= invr,
    pred unit <= unit
    proof *.

  realize addrA by exact SZMod.addrA.
  realize addrC by exact SZMod.addrC.
  realize add0r by exact SZMod.add0r.
  realize addNr by exact SZMod.addNr.

  realize oner_neq0.
  proof.
    apply/negP; rewrite /zeror /oner; move/(congr1 Sub.val).
    by rewrite !Sub.val_insubd sub_0 sub_1 /= CR.oner_neq0.
  qed.

  realize mulrA.
  proof. by move => x y z; rewrite /( * ) !Sub.val_insubd !sub_mul ?Sub.valP //= CR.mulrA. qed.

  realize mulrC.
  proof.
    move => x y; apply/Sub.val_inj.
    by rewrite !Sub.val_insubd !sub_mul ?Sub.valP //= CR.mulrC.
  qed.

  realize mul1r.
  proof.
    move => x; rewrite /oner; apply/Sub.val_inj.
    by rewrite !Sub.val_insubd sub_mul ?Sub.valP //= ?sub_1 //= ?sub_1 //= CR.mul1r.
  qed.

  realize mulrDl.
  proof.
    by move => x y z; rewrite /(+) /( * ) !Sub.val_insubd !sub_add ?sub_mul ?Sub.valP //= CR.mulrDl.
  qed.

  realize mulVr.
  proof. by move => x unit_x; rewrite /( * ) /invr /oner Sub.val_insubd sub_inv ?Sub.valP //= mulVr. qed.

  realize unitP.
  proof.
    move => x y; rewrite /( * ) /oner /unit; move/(congr1 Sub.val); rewrite !Sub.val_insubd.
    by rewrite sub_mul ?Sub.valP //= sub_1 /=; apply/unitP.
  qed.

  realize unitout.
  proof. by move => x; rewrite /unit /invr -{3}(Sub.valKd x) => hnu; apply/congr1/unitout. qed.

end SubComRing.


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
