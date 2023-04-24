(* ==================================================================== *)
require import AllCore List Ring Int IntMin IntDiv Real RealExp Poly.
require import StdBigop StdPoly Binomial Counting Perms.
require import RingStruct SubRing PolyDiv FiniteRing Ideal.
require import PolyFiniteField.
(*---*) import StdOrder.IntOrder.



abstract theory FFexistence.
  type t, st.

  op n : int.

  axiom lt0n: 0 < n.

  clone include PolyFiniteField with
    type t <- st
    rename [theory] "RL"      as "SRL"
                    "ZModStr" as "ZModSStr"
                    "CRStr"   as "CRSStr"
                    "IDStr"   as "IDSStr"
                    "FStr"    as "FSStr"
                    "FT"      as "SFT"
                    "FZMod"   as "FZModS"
                    "FCR"     as "FCRS"
                    "FID"     as "FIDS"
                    "FF"      as "FFS"
                    "UZL"     as "UZLS"
                    "UStr"    as "USStr"
                    "USt"     as "UStS"
                    "FUT"     as "FUTS"
                    "UZModCR" as "USZModCR"
                    "FUZMod"  as "FUSZMod"
           [type]   "uz"      as "uzs".

  import Counting_Argument PolyFinF.

  op is_extension_params1 (mp : int * PID.poly) =
    0 < mp.`1 /\
    PID.irreducible_poly mp.`2 /\
    PID.P.monic mp.`2 /\
    0 < I n (SFT.card ^ (PID.P.deg mp.`2 - 1)).

  op m = (choiceb (is_extension_params1) (0, PID.P.poly0)).`1.

  op p = (choiceb (is_extension_params1) (0, PID.P.poly0)).`2.

  lemma mpP :
    0 < m /\
    PID.irreducible_poly p /\
    PID.P.monic p /\
    0 < I n (SFT.card ^ (PID.P.deg p - 1)).
  proof.
    move: (choicebP is_extension_params1 (0, PID.P.poly0) _); last first.
    + by rewrite /m /p; pose c:= choiceb _ _; move: c => c; rewrite /is_extension_params1.
    rewrite /is_extension_params1; case: (lt0I _ lt0n) => q.
    move: (ilog_eq _ (max 1 q) (ilog SFT.card (max 1 q)) FCRS.card_gt1 _ _) => /=.
    + by apply/gtr_maxrP.
    + by apply/ilog_ge0; [apply/ltzW/FCRS.card_gt1|apply/ger_maxrP].
    rewrite /SFT.card /=.
    case=> _ /ltr_maxrP [] _ /ltzW leq_ lt0I_.
    case: (exists_iu_le_deg (ilog SFT.card (max 1 q) + 1)) => p.
    case=> /ltr_subr_addr /ltzE le_ [] irr_ m_; exists (n, p) => /=.
    rewrite lt0n irr_ m_ /=; apply/lt0I_/(ler_trans _ _ _ leq_)/ler_weexpn2l.
    + by apply/ltzW/FCRS.card_gt1.
    rewrite le_ /=; apply/addr_ge0 => //.
    by apply/ilog_ge0; [apply/ltzW/FCRS.card_gt1|apply/ger_maxrP].
  qed.
  
  lemma lt0m : 0 < m.
  proof. by case: mpP. qed.
  
  lemma irredp_p : PID.irreducible_poly p.
  proof. by case: mpP. qed.
  
  lemma monic_p : PID.P.monic p.
  proof. by case: mpP. qed.
  
  lemma lt0In_ : 0 < I n (SFT.card ^ (PID.P.deg p - 1)).
  proof. by case: mpP. qed.

  clone import FFIrrPolyExt as Ext1 with
    type st         <- st,
    theory SRL      <- SRL,
    theory ZModSStr <- ZModSStr,
    theory CRSStr   <- CRSStr,
    theory IDSStr   <- IDSStr,
    theory FSStr    <- FSStr,
    theory SFT      <- SFT,
    theory FZModS   <- FZModS,
    theory FCRS     <- FCRS,
    theory FIDS     <- FIDS,
    type uzs        <- uzs,
    theory UStS     <- UStS,
    theory UZLS     <- UZLS,
    theory USStr    <- USStr,
    theory USZModCR <- USZModCR,
    theory FUTS     <- FUTS,
    theory FUSZMod  <- FUSZMod,
    theory FFS      <- FFS,
    (*FIXME: Pierre-Yves: anomaly here if using the big clone with theory.*)
    (*theory PID    <- PID.*)
    op PID.CR.unit  <- FFexistence.PID.CR.unit,
    (*theory PID.CR <- PID.CR,*)
    type PID.poly   <- FFexistence.PID.poly,
    theory PID.IDC  <- PID.IDC,
    theory PID.P    <- PID.P,
    theory PID.PS   <- PID.PS,
    theory PID.RPD  <- PID.RPD,
    theory PID.CRD  <- PID.CRD,
    theory PID.RM   <- PID.RM,
    op p            <- p
  proof PID.CR.unitP, irredp_p.

  realize PID.CR.unitP by exact FFexistence.PID.CR.unitP.
  realize irredp_p.
  proof. by move: irredp_p; rewrite /irreducible_poly /eqp /dvdp /modp /edivp. qed.

  clone import PolyFiniteField as PFFE with
    type t         <- Ext1.t,
    theory RL      <- Ext1.TRL,
    theory ZModStr <- Ext1.ZModTStr,
    theory CRStr   <- Ext1.CRTStr,
    theory IDStr   <- Ext1.IDTStr,
    theory FStr    <- Ext1.FTStr,
    theory FT      <- Ext1.TFT,
    theory FZMod   <- Ext1.FZModT,
    theory FCR     <- Ext1.FCRT,
    theory FID     <- Ext1.FIDT,
    type uz        <- Ext1.uzt,
    theory USt     <- Ext1.UStT,
    theory UZL     <- Ext1.UZLT,
    theory UStr    <- Ext1.UTStr,
    theory UZModCR <- Ext1.UTZModCR,
    theory FUT     <- Ext1.FUTT,
    theory FUZMod  <- Ext1.FUTZMod,
    theory FF      <- Ext1.FFT.
  
  op is_extension_params2 (q : PFFE.PID.poly) =
    PFFE.PID.P.deg q = n + 1 /\
    PFFE.PID.irreducible_poly q /\
    PFFE.PID.P.monic q.
  
  op q = choiceb is_extension_params2 PFFE.PID.P.poly0.
  
  lemma qP : is_extension_params2 q.
  proof.
    rewrite /q; apply/choicebP; rewrite /is_extension_params2.
    move: (PFFE.PolyFinF.eqI_size_enum_iudeg _ lt0n) lt0In_.
    rewrite SFF.eq_card_pow_n FFIrrPolyE.eqn => ->.
    case/has_predT/hasP => q [] + _.
    by case/PolyFinF.enum_iudegP => irr_ [] m_ eq_; exists q.
  qed.
  
  lemma eq_degq : PFFE.PID.P.deg q = n + 1.
  proof. by case: qP. qed.
  
  lemma irredp_q : PFFE.PID.irreducible_poly q.
  proof. by case: qP. qed.
  
  lemma monic_q : PFFE.PID.P.monic q.
  proof. by case: qP. qed.

  clone import FFIrrPolyExt as Ext2 with
    type st         <- Ext1.t,
    theory SRL      <- Ext1.TRL,
    theory ZModSStr <- Ext1.ZModTStr,
    theory CRSStr   <- Ext1.CRTStr,
    theory IDSStr   <- Ext1.IDTStr,
    theory FSStr    <- Ext1.FTStr,
    theory SFT      <- Ext1.TFT,
    theory FZModS   <- Ext1.FZModT,
    theory FCRS     <- Ext1.FCRT,
    theory FIDS     <- Ext1.FIDT,
    type uzs        <- Ext1.uzt,
    theory UStS     <- Ext1.UStT,
    theory UZLS     <- Ext1.UZLT,
    theory USStr    <- Ext1.UTStr,
    theory USZModCR <- Ext1.UTZModCR,
    theory FUTS     <- Ext1.FUTT,
    theory FUSZMod  <- Ext1.FUTZMod,
    theory FFS      <- Ext1.FFT,
    (*FIXME: Pierre-Yves: anomaly here if using the big clone with theory.*)
    (*theory PID      <- PFFE.PID.*)
    op PID.CR.unit  <- PFFE.PID.CR.unit,
    (*theory PID.CR <- PFFE.PID.CR,*)
    type PID.poly   <- PFFE.PID.poly,
    theory PID.IDC  <- PFFE.PID.IDC,
    theory PID.P    <- PFFE.PID.P,
    theory PID.PS   <- PFFE.PID.PS,
    theory PID.RPD  <- PFFE.PID.RPD,
    theory PID.CRD  <- PFFE.PID.CRD,
    theory PID.RM   <- PFFE.PID.RM,
    op p            <- q
  proof PID.CR.unitP, irredp_p.

  realize PID.CR.unitP by exact PFFE.PID.CR.unitP.
  realize irredp_p.
  proof. by move: irredp_q; rewrite /irreducible_poly /eqp /dvdp /modp /edivp. qed.

  clone import SubFiniteFieldFrobenius as Ext3 with
    type t          <- Ext2.t,
    type st         <- FFexistence.t,
    theory TRL      <- Ext2.TRL,
    theory ZModTStr <- Ext2.ZModTStr,
    theory CRTStr   <- Ext2.CRTStr,
    theory IDTStr   <- Ext2.IDTStr,
    theory FTStr    <- Ext2.FTStr,
    theory TFT      <- Ext2.TFT,
    theory FZModT   <- Ext2.FZModT,
    theory FCRT     <- Ext2.FCRT,
    theory FIDT     <- Ext2.FIDT,
    type uzt        <- Ext2.uzt,
    theory UStT     <- Ext2.UStT,
    theory UZLT     <- Ext2.UZLT,
    theory UTStr    <- Ext2.UTStr,
    theory UTZModCR <- Ext2.UTZModCR,
    theory FUTT     <- Ext2.FUTT,
    theory FUTZMod  <- Ext2.FUTZMod,
    theory FFT      <- Ext2.FFT.
fail.
  print filter.

  (*TODO: need P to be an op in FFIrr_Ext.*)

  op insub_ x =
    let y = Ext3.Sub.val x in
    if Ext2.Sub.P y
    then
      let z = Ext2.Sub.insubd y in
      if Ext1.Sub.P z
      then Some (Ext1.Sub.insubd z)
      else None
    else None.

  clone include SubFiniteField with
    type t          <- FFexistence.t,
    type st         <- FFexistence.st,
    type uzs        <- FFexistence.uzs,
    theory SRL      <- FFexistence.SRL,
    theory ZModSStr <- FFexistence.ZModSStr,
    theory CRSStr   <- FFexistence.CRSStr,
    theory IDSStr   <- FFexistence.IDSStr,
    theory FSStr    <- FFexistence.FSStr,
    theory SFT      <- FFexistence.SFT,
    theory FZModS   <- FFexistence.FZModS,
    theory FCRS     <- FFexistence.FCRS,
    theory FIDS     <- FFexistence.FIDS,
    theory FFS      <- FFexistence.FFS,
    theory UZLS     <- FFexistence.UZLS,
    theory USStr    <- FFexistence.USStr,
    theory UStS     <- FFexistence.UStS,
    theory USZModCR <- FFexistence.USZModCR,
    theory FUSZMod  <- FFexistence.FUSZMod,
    theory FUTS     <- FFexistence.FUTS,
    pred Sub.P      <= (fun x =>
                         let y = Ext3.Sub.val x in
                         Ext2.Sub.P y /\
                         let z = Ext2.Sub.insubd y in
                         Ext1.Sub.P z),
    op Sub.val      <= Ext3.Sub.insubd \o  Ext2.Sub.val \o Ext1.Sub.val,
(*
    op Sub.insub    <= (fun x => if exists n , x = TRL.ofint n
                                 then Some (ZModP.inzmod
                                             (choiceb (fun n => x = TRL.ofint n) witness))
                                 else None),
*)
    op Sub.wsT      <= (Ext3.Sub.insubd \o  Ext2.Sub.val \o Ext1.Sub.val) witness
    rename [theory] "SRL"      as "Gone"
                    "ZModSStr" as "Gone"
                    "CRSStr"   as "Gone"
                    "IDSStr"   as "IDSStrGone"
                    "FSStr"    as "FSStrGone"
                    "SFT"      as "Gone"
                    "FZModS"   as "Gone"
                    "FCRS"     as "Gone"
                    "FIDS"     as "Gone"
                    "FFS"      as "Gone"
                    "UZLS"     as "Gone"
                    "USStr"    as "Gone"
                    "UStS"     as "Gone"
                    "FUTS"     as "Gone"
                    "USZModCR" as "Gone"
                    "FUSZMod"  as "Gone"
  proof Sub.*, SZMod.*, SCR.*.
  
  realize Sub.insubN.
  proof.
  by move=> x; rewrite /p_ /insub_ /= negb_and; case=> ->.
  qed.
  
  realize Sub.insubT.
  proof.
  move=> x; rewrite /p_ /val_ /insub_ /(\o) /= => -[] p2 p1; rewrite p2 p1 /=.
  rewrite /Ext1.SubFF.SubF.Sub.val Ext1.SubFF.SubF.Sub.val_insubd.
  move: p1; rewrite /Ext1.SubFF.SubF.p => -> /=.
  rewrite /Ext2.SubFF.SubF.Sub.val Ext2.SubFF.SubF.Sub.val_insubd.
  move: p2; rewrite /Ext2.SubFF.SubF.p => -> /=.
  by apply/SubFFExt2.SubF.Sub.valKd.
  qed.
  
  realize Sub.valP.
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
  
  realize Sub.valK.
  proof.
  move=> x; rewrite /val_ /insub_ /(\o) /=.
  admit.
  qed.
  
  realize Sub.insubW.
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
end FFexistence.

