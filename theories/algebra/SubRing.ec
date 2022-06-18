require import AllCore List Ring Int IntDiv Characteristic Bigalg.
require (*--*) Subtype.
(*---*) import StdOrder.IntOrder.


abstract theory SubZModule.

  clone import ZModule as ZMod.

  type sz.

  op w : ZMod.t.

  pred in_subzmod : ZMod.t.

  axiom sub_w : in_subzmod w.
  axiom sub_add x y : in_subzmod x => in_subzmod y => in_subzmod (x + y).
  axiom sub_opp x : in_subzmod x => in_subzmod (-x).

  lemma sub_0 : in_subzmod zeror.
  proof. by rewrite -(subrr w); apply/sub_add; [apply/sub_w|apply/sub_opp/sub_w]. qed.

  clone Subtype as Sub with
    type T <- ZMod.t,
    type sT <- sz,
    pred P <- in_subzmod.

  op zeror = Sub.insubd zeror.
  op (+) x y = Sub.insubd (Sub.val x + Sub.val y).
  op ([-]) x = Sub.insubd (- Sub.val x).

  clone import ZModule as SZMod with
    type t    <- sz,
    op zeror  <- zeror,
    op (+)    <- (+),
    op [-]  <- ([-])
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
    move => x; rewrite /zeror /([-]); apply/Sub.val_inj.
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
  axiom sub_wu : in_subzmod wu.
  axiom sub_mul x y : in_subzmod x => in_subzmod y => in_subzmod (x * y).
  axiom sub_inv x : in_subzmod x => in_subzmod (invr x).

  lemma sub_1 : in_subzmod oner.
  proof. by rewrite -(mulVr _ unit_wu); apply/sub_mul; [apply/sub_inv/sub_wu|apply/sub_wu]. qed.

  op oner = Sub.insubd oner.
  op ( * ) x y = Sub.insubd (Sub.val x * Sub.val y).
  op invr x = Sub.insubd (invr (Sub.val x)).
  pred unit x = unit (Sub.val x).

  clone import ComRing as SCR with
    type t    <- sz,
    op zeror  <- zeror,
    op (+)    <- (+),
    op [-]    <- ([-]),
    op oner   <- oner,
    op ( * )  <- ( * ),
    op invr   <- invr,
    pred unit <- unit
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
  proof.
    move => x unit_x.
    admit.
  qed.

  realize unitP.
  proof.
    admit.
  qed.

  realize unitout.
  proof.
    admit.
  qed.

end SubComRing.
