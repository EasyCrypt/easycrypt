(* -------------------------------------------------------------------- *)
require import AllCore List Ring Int IntDiv Bigalg RingStruct.
require (*--*) Subtype.
(*---*) import StdOrder.IntOrder.



(* ==================================================================== *)
abstract theory UZMod_ComRing.
  type t, uz.

  clone include ComRingStruct with
    type t <- t.

  import RL.

  clone import Subtype as Sub with
    type T  <= t,
    type sT <= uz,
    pred P  <= unit.

  clone import ZModule as UZMod with
    type t    <= uz,
    op zeror  <= insubd oner,
    op (+)    <= (fun x y => insubd (val x * val y)),
    op [-]    <= (fun x => insubd (invr (val x)))
    proof *.

  realize addrA.
  proof.
    move=> x y z; rewrite /( + ); apply/val_inj.
    rewrite !val_insubd !unitrM !valP /= !unitrM !valP /=.
    by rewrite mulrA.
  qed.

  realize addrC.
  proof.
    move=> x y; rewrite /( + ); apply/val_inj.
    rewrite !val_insubd !unitrM !valP /=.
    by rewrite mulrC.
  qed.

  realize add0r.
  proof.
    move=> x; rewrite /zeror /( + ); apply/val_inj.
    by rewrite !val_insubd unitr1 /= mul1r valP.
  qed.

  realize addNr.
  proof.
    move=> x; rewrite /zeror /( + ) /([-]); apply/val_inj; rewrite !val_insubd.
    by rewrite unitrV valP /= unitrM unitrV valP unitr1 /= mulVr // valP.
  qed.

  theory UZModCR.
    import Sub.

    lemma val1 : val UZMod.zeror = RL.oner.
    proof. by rewrite val_insubd unitr1. qed.

    lemma valM x y : val (UZMod.( + ) x y) = val x * val y.
    proof. by rewrite /( + ) val_insubd unitrM !valP. qed.

    lemma valV x : val (UZMod.([-]) x) = invr (val x).
    proof. by rewrite /UZMod.([-]) val_insubd unitrV valP. qed.

    lemma valXR x n :
      0 <= n =>
      val (UZMod.intmul x n) = exp (val x) n.
    proof.
      elim n => [|n le0n IHn]; [by rewrite mulr0z expr0 val1|].
      by rewrite mulrSz valM IHn exprS.
    qed.
  end UZModCR.
end UZMod_ComRing.

(* -------------------------------------------------------------------- *)
abstract theory UZMod_IDomain.
  type t, uz.

  clone include IDomainStruct with
    type t <- t.

  clone include UZMod_ComRing with
    type t    <- t,
    type uz   <- uz,
    theory RL <- RL,
    theory ZModStr <- ZModStr,
    theory CRStr   <- CRStr
    rename [theory] "RL"  as "Gone"
           [theory] "Str" as "Gone".
end UZMod_IDomain.

(* -------------------------------------------------------------------- *)
abstract theory UZMod_Field.
  type t, uz.

  clone include FieldStruct with
    type t <- t.

  clone include UZMod_IDomain with
    type t    <- t,
    type uz   <- uz,
    theory RL <- RL,
    theory ZModStr <- ZModStr,
    theory CRStr   <- CRStr,
    theory IDStr   <- IDStr
    rename [theory] "RL"  as "Gone"
           [theory] "Str" as "Gone".

  theory UZModF.
    import RL Sub UZModCR.
    lemma valX x n :
      val (UZMod.intmul x n) = exp (val x) n.
    proof.
      case (0 <= n) => [|/ltrNge/ltzW]; [by apply/valXR|].
      rewrite -(IntID.opprK n) oppr_le0 => le0_.
      by rewrite UZMod.mulrNz valV exprN; congr; apply/valXR.
    qed.
  end UZModF.
end UZMod_Field.

