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

  clone import Subtype as USt with
    type T  <= t,
    type sT <= uz,
    pred P  <= unit.

  clone include ZModuleStruct with
    type t       <- uz,
    op RL.zeror  <= insubd oner,
    op RL.(+)    <= (fun x y => insubd (val x * val y)),
    op RL.([-])  <= (fun x => insubd (invr (val x)))
    rename [theory] "RL"      as "UZL"
                    "ZModStr" as "UStr"
  proof *.

  realize UZL.addrA.
  proof.
    move=> x y z; rewrite /( + ); apply/val_inj.
    rewrite !val_insubd !unitrM !valP /= !unitrM !valP /=.
    by rewrite mulrA.
  qed.

  realize UZL.addrC.
  proof.
    move=> x y; rewrite /( + ); apply/val_inj.
    rewrite !val_insubd !unitrM !valP /=.
    by rewrite mulrC.
  qed.

  realize UZL.add0r.
  proof.
    move=> x; rewrite /zeror /( + ); apply/val_inj.
    by rewrite !val_insubd unitr1 /= mul1r valP.
  qed.

  realize UZL.addNr.
  proof.
    move=> x; rewrite /zeror /( + ) /([-]); apply/val_inj; rewrite !val_insubd.
    by rewrite unitrV valP /= unitrM unitrV valP unitr1 /= mulVr // valP.
  qed.

  theory UZModCR.
    import USt UZL.

    lemma val1 : val UZL.zeror = RL.oner.
    proof. by rewrite val_insubd unitr1. qed.

    lemma valM x y : val (UZL.( + ) x y) = val x * val y.
    proof. by rewrite /( + ) val_insubd unitrM !valP. qed.

    lemma valV x : val (UZL.([-]) x) = invr (val x).
    proof. by rewrite /UZL.([-]) val_insubd unitrV valP. qed.

    lemma valX x n :
      val (UZL.intmul x n) = exp (val x) n.
    proof.
      wlog: n / 0 <= n => [wlogn|].
      + case (0 <= n) => [/wlogn //|] /ltrNge/ltzW/ler_opp2/=/wlogn {wlogn}.
        by rewrite exprN mulrNz valV => /invr_inj.
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
    rename [theory] "RL"      as "Gone"
           [theory] "ZModStr" as "Gone"
           [theory] "CRStr"   as "Gone".
end UZMod_IDomain.

(* -------------------------------------------------------------------- *)
abstract theory UZMod_Field.
  type t, uz.

  clone include FieldStruct with
    type t <- t.

  clone include UZMod_IDomain with
    type t         <- t,
    type uz        <- uz,
    theory RL      <- RL,
    theory ZModStr <- ZModStr,
    theory CRStr   <- CRStr,
    theory IDStr   <- IDStr
    rename [theory] "RL"  as "Gone"
           [theory] "ZModStr" as "Gone"
           [theory] "CRStr"   as "Gone"
           [theory] "IDStr"   as "UZMod_FieldIDStrGone".
end UZMod_Field.

