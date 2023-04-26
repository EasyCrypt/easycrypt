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
                    "UZModCR" as "UZModCRS"
                    "FUZMod"  as "FUZModS"
           [type]   "uz"      as "uzs".

  clone import SubFiniteField_ZMod as SFF_ZMod with
    type t <- st,
    theory TRL      <- SRL,
    theory ZModTStr <- ZModSStr,
    theory CRTStr   <- CRSStr,
    theory IDTStr   <- IDSStr,
    theory FTStr    <- FSStr,
    theory TFT      <- SFT,
    theory FZModT   <- FZModS,
    theory FCRT     <- FCRS,
    theory FIDT     <- FIDS,
    type uzt        <- uzs,
    theory UStT     <- UStS,
    theory UZLT     <- UZLS,
    theory UTStr    <- USStr,
    theory UZModCRT <- UZModCRS,
    theory FUTT     <- FUTS,
    theory FUZModT  <- FUZModS,
    theory FFT      <- FFS.

  import Counting_Argument PolyFinF.

  op is_extension_params1 (mp : int * PID.poly) =
    0 < mp.`1 /\
    PID.irreducible_poly mp.`2 /\
    PID.P.monic mp.`2 /\
    0 < I n (FFexistence.SFT.card ^ (PID.P.deg mp.`2 - 1)).

  op m = (choiceb (is_extension_params1) (0, PID.P.poly0)).`1.

  op p = (choiceb (is_extension_params1) (0, PID.P.poly0)).`2.

  lemma mpP :
    0 < m /\
    PID.irreducible_poly p /\
    PID.P.monic p /\
    0 < I n (FFexistence.SFT.card ^ (PID.P.deg p - 1)).
  proof.
    move: (choicebP is_extension_params1 (0, PID.P.poly0) _); last first.
    + by rewrite /m /p; pose c:= choiceb _ _; move: c => c; rewrite /is_extension_params1.
    rewrite /is_extension_params1; case: (lt0I _ lt0n) => q.
    move: (ilog_eq _ (max 1 q) (ilog FFexistence.SFT.card (max 1 q)) FFexistence.FCRS.card_gt1 _ _) => /=.
    + by apply/gtr_maxrP.
    + by apply/ilog_ge0; [apply/ltzW/FFexistence.FCRS.card_gt1|apply/ger_maxrP].
    rewrite /FFexistence.SFT.card /=.
    case=> _ /ltr_maxrP [] _ /ltzW leq_ lt0I_.
    case: (exists_iu_le_deg (ilog FFexistence.SFT.card (max 1 q) + 1)) => p.
    case=> /ltr_subr_addr /ltzE le_ [] irr_ m_; exists (n, p) => /=.
    rewrite lt0n irr_ m_ /=; apply/lt0I_/(ler_trans _ _ _ leq_)/ler_weexpn2l.
    + by apply/ltzW/FFexistence.FCRS.card_gt1.
    rewrite le_ /=; apply/addr_ge0 => //.
    by apply/ilog_ge0; [apply/ltzW/FFexistence.FCRS.card_gt1|apply/ger_maxrP].
  qed.
  
  lemma lt0m : 0 < m.
  proof. by case: mpP. qed.
  
  lemma irredp_p : PID.irreducible_poly p.
  proof. by case: mpP. qed.
  
  lemma monic_p : PID.P.monic p.
  proof. by case: mpP. qed.
  
  lemma lt0In_ : 0 < I n (FFexistence.SFT.card ^ (PID.P.deg p - 1)).
  proof. by case: mpP. qed.

  clone import FFIrrPolyExt as Ext1 with
    type st         <- FFexistence.st,
    theory SRL      <- FFexistence.SRL,
    theory ZModSStr <- FFexistence.ZModSStr,
    theory CRSStr   <- FFexistence.CRSStr,
    theory IDSStr   <- FFexistence.IDSStr,
    theory FSStr    <- FFexistence.FSStr,
    theory SFT      <- FFexistence.SFT,
    theory FZModS   <- FFexistence.FZModS,
    theory FCRS     <- FFexistence.FCRS,
    theory FIDS     <- FFexistence.FIDS,
    type uzs        <- FFexistence.uzs,
    theory UStS     <- FFexistence.UStS,
    theory UZLS     <- FFexistence.UZLS,
    theory USStr    <- FFexistence.USStr,
    theory UZModCRS <- FFexistence.UZModCRS,
    theory FUTS     <- FFexistence.FUTS,
    theory FUZModS  <- FFexistence.FUZModS,
    theory FFS      <- FFexistence.FFS,
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
    theory UZModCR <- Ext1.UZModCRT,
    theory FUT     <- Ext1.FUTT,
    theory FUZMod  <- Ext1.FUZModT,
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
    theory UZModCRS <- Ext1.UZModCRT,
    theory FUTS     <- Ext1.FUTT,
    theory FUZModS  <- Ext1.FUZModT,
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
    theory UZModCRT <- Ext2.UZModCRT,
    theory FUTT     <- Ext2.FUTT,
    theory FUZModT  <- Ext2.FUZModT,
    theory FFT      <- Ext2.FFT,
    op n            <- FFexistence.n * SFF_ZMod.SFF.n.

  clone include SubFiniteField with
    type t          <- FFexistence.t,
    type st         <- FFexistence.st,
    type uzt        <- Ext3.uzs,
    type uzs        <- FFexistence.uzs,
    theory TRL      <= Ext3.SRL,
    theory ZModTStr <= Ext3.ZModSStr,
    theory CRTStr   <= Ext3.CRSStr,
    theory IDTStr   <= Ext3.IDSStr,
    theory FTStr    <= Ext3.FSStr,
    theory TFT      <= Ext3.SFT,
    theory FZModT   <= Ext3.FZModS,
    theory FCRT     <= Ext3.FCRS,
    theory FIDT     <= Ext3.FIDS,
    theory FFT      <= Ext3.FFS,
    theory UZLT     <= Ext3.UZLS,
    theory UTStr    <= Ext3.USStr,
    theory UStT     <= Ext3.UStS,
    theory UZModCRT <= Ext3.UZModCRS,
    theory FUZModT  <= Ext3.FUZModS,
    theory FUTT     <= Ext3.FUTS,
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
    theory UZModCRS <- FFexistence.UZModCRS,
    theory FUZModS  <- FFexistence.FUZModS,
    theory FUTS     <- FFexistence.FUTS,
    pred Sub.P      <= (fun x =>
                         let y = Ext3.Sub.val x in
                         Ext2.Sub.P y /\
                         let z = Ext2.Sub.insubd y in
                         Ext1.Sub.P z),
    op Sub.insub    <= (fun x =>
                         let y = Ext3.Sub.val x in
                         if Ext2.P y
                         then
                           let z = Ext2.Sub.insubd y in
                           if Ext1.P z
                           then Some (Ext1.Sub.insubd z)
                           else None
                         else None),
    op Sub.val      <= Ext3.Sub.insubd \o  Ext2.Sub.val \o Ext1.Sub.val,
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
                    "UZModCRS" as "Gone"
                    "FUZModS"  as "Gone"
  proof Sub.*, SZMod.*, SCR.*.
  
  realize Sub.insubN.
  proof.
    by move=> x; rewrite /P /insub /= negb_and; case=> ->.
  qed.
  
  realize Sub.insubT.
  proof.
    move=> x; rewrite /P /val /insub /(\o) /= => -[] p2 p1; rewrite p2 p1 /=.
    rewrite /Ext1.Sub.val Ext1.Sub.val_insubd.
    move: p1; rewrite /Ext1.P => -> /=.
    rewrite /Ext2.Sub.val Ext2.Sub.val_insubd.
    move: p2; rewrite /Ext2.P => -> /=.
    by apply/Ext3.Sub.valKd.
  qed.
  
  realize Sub.valP.
  proof.
    move=> x; rewrite /(\o) /= Ext3.Sub.val_insubd ifT.
    + rewrite Ext2.SID.val_iter_frobenius_fixed Ext1.SID.val_iter_frobenius_fixed.
      apply/FFexistence.IDSStr.iter_frobenius_fixed_imp.
      - by apply/ltzW/lt0n.
      - by apply/ltzW/SFF_ZMod.SFF.lt0n.
      by rewrite FinZMod.iter_frobenius_fixed_n /predT.
    split; [by apply/ Ext2.Sub.valP|].
    by rewrite Ext2.Sub.valKd; apply/Ext1.Sub.valP.
  qed.
  
  realize Sub.valK.
  proof.
    move=> x; rewrite /(\o) /= Ext3.Sub.val_insubd.
    rewrite Ext2.SID.val_iter_frobenius_fixed Ext1.SID.val_iter_frobenius_fixed.
    rewrite FFexistence.IDSStr.iter_frobenius_fixed_imp /=.
    + by apply/ltzW/lt0n.
    + by apply/ltzW/SFF_ZMod.SFF.lt0n.
    + by rewrite FinZMod.iter_frobenius_fixed_n /predT.
    by rewrite Ext2.Sub.valP /= Ext2.Sub.valKd Ext1.Sub.valP /= Ext1.Sub.valKd.
  qed.
  
  realize Sub.insubW.
  proof.
    rewrite /(\o) /= Ext3.Sub.val_insubd.
    rewrite Ext2.SID.val_iter_frobenius_fixed Ext1.SID.val_iter_frobenius_fixed.
    rewrite FFexistence.IDSStr.iter_frobenius_fixed_imp /=.
    + by apply/ltzW/lt0n.
    + by apply/ltzW/SFF_ZMod.SFF.lt0n.
    + by rewrite FinZMod.iter_frobenius_fixed_n /predT.
    by rewrite Ext2.Sub.valP /= Ext2.Sub.valKd Ext1.Sub.valP /= Ext1.Sub.valKd.
  qed.

  realize SZMod.val0.
  proof. by rewrite /morphism_0 /(\o) /Ext1.Sub.val Ext1.SZMod.val0 /Ext2.Sub.val Ext2.SZMod.val0. qed.

  realize SZMod.valD.
  proof.
    move=> x y; rewrite /(\o) /= /Ext1.Sub.val Ext1.SZMod.valD /Ext2.Sub.val Ext2.SZMod.valD.
    rewrite !Ext3.Sub.val_insubd !Ext2.SID.val_iter_frobenius_fixed !Ext1.SID.val_iter_frobenius_fixed.
    rewrite !FFexistence.IDSStr.iter_frobenius_fixed_imp //.
    + by apply/ltzW/lt0n.
    + by apply/ltzW/SFF_ZMod.SFF.lt0n.
    + by rewrite FinZMod.iter_frobenius_fixed_n /predT.
    + by apply/ltzW/lt0n.
    + by apply/ltzW/SFF_ZMod.SFF.lt0n.
    by rewrite FinZMod.iter_frobenius_fixed_n /predT.
  qed.

  realize SCR.val1.
  proof. by rewrite /morphism_0 /(\o) /Ext1.Sub.val Ext1.SCR.val1 /Ext2.Sub.val Ext2.SCR.val1. qed.

  realize SCR.valM.
  proof.
    move=> x y; rewrite /(\o) /= /Ext1.Sub.val Ext1.SCR.valM /Ext2.Sub.val Ext2.SCR.valM.
    rewrite !Ext3.Sub.val_insubd !Ext2.SID.val_iter_frobenius_fixed !Ext1.SID.val_iter_frobenius_fixed.
    rewrite !FFexistence.IDSStr.iter_frobenius_fixed_imp //.
    + by apply/ltzW/lt0n.
    + by apply/ltzW/SFF_ZMod.SFF.lt0n.
    + by rewrite FinZMod.iter_frobenius_fixed_n /predT.
    + by apply/ltzW/lt0n.
    + by apply/ltzW/SFF_ZMod.SFF.lt0n.
    by rewrite FinZMod.iter_frobenius_fixed_n /predT.
  qed.

  lemma generator_extension_enum g :
    Ext2.UTStr.is_generator g =>
    perm_eq
      Ext3.SFT.enum
      (Ext3.SRL.zeror ::
       map
         ( Ext3.Sub.insubd \o
           Ext2.UStT.val \o
           (Ext2.UZLT.intmul
             (Ext2.UZLT.intmul
               g
               ( (FFexistence.CRSStr.char ^ (Ext1.SFF.n * (FFexistence.n * SFF_ZMod.SFF.n)) - 1) %/
                 (FFexistence.CRSStr.char ^ (FFexistence.n * SFF_ZMod.SFF.n) - 1)))))
         (range 0 (FFexistence.CRSStr.char ^ (FFexistence.n * SFF_ZMod.SFF.n) - 1))).
  proof.
    move=> is_g_g.
    have eq_ucard: Ext2.FUTT.card =
             (FFexistence.CRSStr.char ^ (Ext1.SFF.n * (FFexistence.n * SFF_ZMod.SFF.n)) - 1).
    + rewrite mulrA mulrAC (mulrC _ SFF_ZMod.SFF.n) -mulrA exprM -ZModFin.eq_card_p.
      rewrite -SFF_ZMod.SFF.eq_card_pow_n exprM -Ext1.SFF.eq_card_pow_n.
      move: Ext2.SFF.eq_card_pow_n; rewrite FFIrrPolyE.eqn eq_degq /= => <-.
      by rewrite Ext2.FFT.card_unit.
    have dvdB_1: (FFexistence.CRSStr.char ^ (n * SFF_ZMod.SFF.n) - 1) %|
          (FFexistence.CRSStr.char ^ (Ext1.SFF.n * (n * SFF_ZMod.SFF.n)) - 1).
    + rewrite -!(opprB 1); apply/dvdzN/dvdNz.
      rewrite (mulrC Ext1.SFF.n) (exprM _ _ Ext1.SFF.n).
      rewrite (Bigint.BIA.geo_sum Ext1.SFF.n).
      - by apply/ltzW/Ext1.SFF.lt0n.
      by apply/dvdz_mulr/dvdzz.
    apply/uniq_perm_eq => /=; [|split|].
    + by apply/FFexistence.TFT.enum_uniq.
    + rewrite mapP negb_exists => x /=; rewrite negb_and /(\o) /= -Ext2.UZLT.mulrM; right.
      apply/negP => /(congr1 TRL.unit); rewrite {1}/TRL.unit -FFexistence.TRL.unitfE.
      rewrite /SRL.zeror /= eq_sym neqF negbK /TRL.unit Ext3.SFld.insubdU; last first.
      - by apply/Ext2.UStT.valP.
      rewrite Ext2.IDTStr.iter_frobenius_fixedP.
      - by apply/mulr_ge0; apply/ltzW; [apply/lt0n|apply/SFF_ZMod.SFF.lt0n].
      rewrite -Ext2.UZModCRT.valX -Ext2.UZLT.mulrM; congr; apply/Ext2.UTStr.dvd2_order.
      move/Ext2.FUZModT.isgeneratorP: (is_g_g) => ->; pose y:= _ %/ _ * _.
      rewrite -{2}(mulr1 y) -mulrN -mulrDr /y => {y}; rewrite -Ext3.SCR.eq_char -SCR.eq_char.
      rewrite mulrAC; apply/dvdz_mulr; rewrite divzK //.
      by rewrite eq_ucard dvdzz.
    + apply/map_inj_in_uniq; [|by apply/range_uniq].
      move=> x y memx memy; rewrite /(\o) /= => /(congr1 Ext3.Sub.val).
      rewrite !Ext3.Sub.val_insubd !ifT.
      - apply/Ext2.IDTStr.iter_frobenius_fixedP.
        * by apply/mulr_ge0; apply/ltzW; [apply/lt0n|apply/SFF_ZMod.SFF.lt0n].
        rewrite -Ext2.UZLT.mulrM -Ext2.UZModCRT.valX -Ext2.UZLT.mulrM.
        congr; apply/Ext2.UTStr.dvd2_order.
        move/Ext2.FUZModT.isgeneratorP: (is_g_g) => ->; pose z:= _ %/ _ * _.
        rewrite -{2}(mulr1 z) -mulrN -mulrDr /z => {z}.
        rewrite -Ext3.SCR.eq_char -SCR.eq_char.
        rewrite mulrAC; apply/dvdz_mulr; rewrite divzK //.
        by rewrite eq_ucard dvdzz.
      - apply/Ext2.IDTStr.iter_frobenius_fixedP.
        * by apply/mulr_ge0; apply/ltzW; [apply/lt0n|apply/SFF_ZMod.SFF.lt0n].
        rewrite -Ext2.UZLT.mulrM -Ext2.UZModCRT.valX -Ext2.UZLT.mulrM.
        congr; apply/Ext2.UTStr.dvd2_order.
        move/Ext2.FUZModT.isgeneratorP: (is_g_g) => ->; pose z:= _ %/ _ * _.
        rewrite -{2}(mulr1 z) -mulrN -mulrDr /z => {z}.
        rewrite -Ext3.SCR.eq_char -SCR.eq_char.
        rewrite mulrAC; apply/dvdz_mulr; rewrite divzK //.
        by rewrite eq_ucard dvdzz.
      move/Ext2.UStT.val_inj/Ext2.UTStr.dvd2_order.
      move/Ext2.FUZModT.isgeneratorP: (is_g_g) => eq_.
      rewrite Ext2.UTStr.order_intmul eq_; [by apply/Ext2.FUTT.card_gt0|].
      have ->//: forall a b c , 0 < a => 0 < c => a = b => c %| b => a %/ gcd a (b %/ c) = c.
      - move=> a ? b lt0a lt0b <<- dvdba; rewrite gcd_dvdr.
        * by apply/dvdz_div => //; apply/gtr_eqF.
        rewrite gtr0_norm; [by apply/ltz_divRL|].
        rewrite -mulz_divl //; [by apply/ltzW|].
        by apply/mulzK/gtr_eqF.
      - by apply/Ext2.FUTT.card_gt0.
      - apply/subr_gt0/exprn_egt1.
        * by apply/mulr_ge0; apply/ltzW; [apply/lt0n|apply/SFF_ZMod.SFF.lt0n].
        * by apply/FFexistence.FCRS.gt1_char.
        by apply/gtr_eqF/mulr_gt0; [apply/lt0n|apply/SFF_ZMod.SFF.lt0n].
      by rewrite eq_mod !modz_small -?mem_range ?ger0_norm //;
      apply/ltzS => /=; apply/expr_gt0/FFexistence.FCRS.gt0_char.
    move=> x; rewrite SFT.enumP /= -implyNb => /TRL.unitfP ux.
    rewrite !map_comp -Ext3.Sub.valKd; apply/map_f.
    move: (Ext2.UStT.val_insubd (Ext3.Sub.val x)).
    rewrite ifT. apply/negP => eq_; move: ux; rewrite eq_ => /= {eq_}.
    + by rewrite negb_exists => y /=; rewrite IFQ.FQ.mulr0 eq_sym IFQ.FQ.oner_neq0.
    move=> <-; apply/map_f; case/(_ (Ext2.UStT.insubd (Ext3.Sub.val x))): (is_g_g).
    move=> m; rewrite -Ext2.UTStr.intmul_modz_order.
    move/Ext2.FUZModT.isgeneratorP: (is_g_g) => ->.
    pose k := m %% Ext2.FUTT.card.
    have: k \in range 0 Ext2.FUTT.card; rewrite /k => {k}.
    + apply/mem_range; rewrite modz_ge0 /=.
      - by apply/gtr_eqF/Ext2.FUTT.card_gt0.
      by apply/ltz_pmod/Ext2.FUTT.card_gt0.
    rewrite eq_ucard.
    pose k := _ %% _; move: k => {m} m mem_m eq_.
    rewrite eq_; move: eq_.
    move/(congr1 (transpose Ext2.UZLT.intmul
                            (FFexistence.CRSStr.char ^ (n * SFF_ZMod.SFF.n) - 1))).
    rewrite /= -Ext2.UZModCRT.insubdX; [by rewrite Ext3.SFld.valU|].
    rewrite {1}Ext1.SCR.eq_char {1}Ext2.SCR.eq_char.
    move: (Ext2.IDTStr.iter_frobenius_fixedP (n * SFF_ZMod.SFF.n) (Ext3.Sub.val x) _).
    + by apply/ltzW/mulr_gt0; [apply/lt0n|apply/SFF_ZMod.SFF.lt0n].
    rewrite Ext3.Sub.valP /=.
    rewrite IFQ.FQ.exprD; [by rewrite Ext3.SFld.valU|].
    move=> ->; rewrite -{1}(IFQ.FQ.expr1 (Ext3.Sub.val x)).
    rewrite -IFQ.FQ.exprD /=; [by rewrite Ext3.SFld.valU|].
    rewrite IFQ.FQ.expr0 -(Ext2.UZLT.mulr0z g).
    rewrite -(Ext2.UZLT.mulrM g m (_ - 1)).
    move/eq_sym/Ext2.UTStr.dvd2_order => /=.
    move/Ext2.FUZModT.isgeneratorP: is_g_g => ->.
    rewrite eq_ucard dvdzP => -[q].
    move/(congr1 (transpose (%/) (FFexistence.CRSStr.char ^ (n * SFF_ZMod.SFF.n) - 1))).
    rewrite /= mulzK.
    + apply/gtr_eqF/subr_gt0; rewrite exprn_egt1.
      - by apply/mulr_ge0; apply/ltzW; [apply/lt0n|apply/SFF_ZMod.SFF.lt0n].
      - by apply/FFexistence.FCRS.gt1_char.
      by apply/gtr_eqF/mulr_gt0; [apply/lt0n|apply/SFF_ZMod.SFF.lt0n].
    move=> ->>; move: mem_m; rewrite divMr // mem_range_mulr.
    + apply/ltz_divRL => //=.
      - apply/subr_gt0; rewrite exprn_egt1.
        * by apply/mulr_ge0; apply/ltzW; [apply/lt0n|apply/SFF_ZMod.SFF.lt0n].
        * by apply/FFexistence.FCRS.gt1_char.
        by apply/gtr_eqF/mulr_gt0; [apply/lt0n|apply/SFF_ZMod.SFF.lt0n].
      apply/subr_gt0; rewrite exprn_egt1.
      - apply/ltzW/mulr_gt0; [|apply/mulr_gt0].
        * by apply/Ext1.SFF.lt0n.
        * by apply/lt0n.
        by apply/SFF_ZMod.SFF.lt0n.
      - by apply/FFexistence.FCRS.gt1_char.
      apply/gtr_eqF/mulr_gt0; [|apply/mulr_gt0].
      - by apply/Ext1.SFF.lt0n.
      - by apply/lt0n.
      by apply/SFF_ZMod.SFF.lt0n.
    rewrite /=; have ->//: forall a b , a <> 0 => 0 <= b => b %| a => a %\ (a %/ b) = b.
    + by move=> a b neqa0 le0b dvdba; rewrite -mulz_divl // mulrN -mulNr mulzK.
    + apply/gtr_eqF/subr_gt0; rewrite exprn_egt1.
      - apply/ltzW/mulr_gt0; [|apply/mulr_gt0].
        * by apply/Ext1.SFF.lt0n.
        * by apply/lt0n.
        by apply/SFF_ZMod.SFF.lt0n.
      - by apply/FFexistence.FCRS.gt1_char.
      apply/gtr_eqF/mulr_gt0; [|apply/mulr_gt0].
      - by apply/Ext1.SFF.lt0n.
      - by apply/lt0n.
      by apply/SFF_ZMod.SFF.lt0n.
    + by apply/ltzS => /=; apply/expr_gt0/FFexistence.FCRS.gt0_char.
    move=> mem_q; rewrite (mulrC q) Ext2.UZLT.mulrM.
    by apply/mapP; exists q.
  qed.

  lemma eqn : FFexistence.n = FFexistence.SFF.n.
  proof.
    case: Ext2.FFT.exists_generator => g is_g_g.
    move: FFexistence.SFF.eq_card_pow_n.
    move: (generator_extension_enum _ is_g_g).
    move/perm_eq_size; rewrite -/SFT.card => -> /=.
    rewrite size_map size_range /= (addrC 1) ler_maxr /=.
    + by apply/ltzS => /=; apply/expr_gt0/FFexistence.FCRS.gt0_char.
    rewrite mulrC exprM -ZModFin.eq_card_p -SFF_ZMod.SFF.eq_card_pow_n.
    apply/ieexprIn; [by apply/FFexistence.SFT.card_gt0| | |].
    + by apply/gtr_eqF/FFexistence.FCRS.card_gt1.
    + by apply/ltzW/lt0n.
    by apply/ltzW/SFF.lt0n.
  qed.
end FFexistence.

