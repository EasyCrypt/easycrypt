(* -------------------------------------------------------------------- *)
require import AllCore List Ring Int IntDiv Bigalg RingStruct RingMorph.
require (*--*) Subtype.
(*---*) import StdOrder.IntOrder.



(* ==================================================================== *)
abstract theory SubZModule.
  type t, st.

  clone include ZModuleStruct with
    type t <- t
    rename [theory] "RL"  as "TRL"
           [theory] "Str" as "TStr".

  clone include ZModuleStruct with
    type t <- st
    rename [theory] "RL"  as "SRL"
           [theory] "Str" as "SStr".

  clone include ZModuleMorph with
    type t1 <- st,
    type t2 <- t,
    theory RL1 <- SRL,
    theory RL2 <- TRL,
    theory ZModStr1 <- ZModSStr,
    theory ZModStr2 <- ZModTStr.

  clone import Subtype as Sub with
    type T  <= t ,
    type sT <= st.

  theory SZMod.
    import Sub TRL SRL ZModTStr ZModSStr ZModMorph.

    axiom val0 : morphism_0 val SRL.zeror TRL.zeror.

    axiom valD : morphism_2 val SRL.(+) TRL.(+).

    lemma val_zmod_homo : zmod_homo val.
    proof. by split; [apply/val0|apply/valD]. qed.

    lemma val_zmod_mono : zmod_mono val.
    proof. by split; [apply/val_inj|apply/val_zmod_homo]. qed.

    lemma valN :
      morphism_1 val SRL.([-]) TRL.([-]).
    proof. by apply/zmod_monoN/val_zmod_mono. qed.

    lemma valB :
      morphism_2 val SRL.( - ) TRL.( - ).
    proof. by apply/zmod_monoB/val_zmod_mono. qed.

    lemma valMz :
      forall x n , val (SRL.intmul x n) = intmul (val x) n.
    proof. by apply/zmod_monoMz/val_zmod_mono. qed.

    lemma val_eq0 :
      forall x , val x = TRL.zeror <=> x = SRL.zeror.
    proof. by apply/zmod_mono_eq0/val_zmod_mono. qed.

    lemma val_order :
      forall x , order (val x) = order x.
    proof. by apply/zmod_mono_order/val_zmod_mono. qed.

    lemma val_orbit :
      forall x y ,
        orbit (val x) (val y) = orbit x y.
    proof. by apply/zmod_mono_orbit/val_zmod_mono. qed.
  
    lemma val_orbit_list :
      forall x ,
        orbit_list (val x) = map val (orbit_list x).
    proof. by apply/zmod_mono_orbit_list/val_zmod_mono. qed.
  
    lemma val_eqv_orbit :
      forall x y z ,
        eqv_orbit (val x) (val y) (val z) =
        eqv_orbit x y z.
    proof. by apply/zmod_mono_eqv_orbit/val_zmod_mono. qed.

    lemma subzmodP : subzmod P.
    proof.
      move: (subzmod_zmod_mono_subzmod _ _ val_zmod_mono subzmodT).
      apply/eq_ind/fun_ext => y; apply/eq_iff; split=> [[x] [] <<- _|Py].
      + by apply/valP.
      by exists (insubd y); rewrite val_insubd Py.
    qed.

    lemma P0 : P TRL.zeror.
    proof. by apply/ZModTStr.subzmod0/subzmodP. qed.
  
    lemma PD x y : P x => P y => P (TRL.( + ) x y).
    proof. by move: x y; apply/ZModTStr.subzmodD/subzmodP. qed.
  
    lemma PN x : P x => P (TRL.([-]) x).
    proof. by move: x; apply/ZModTStr.subzmodN/subzmodP. qed.
  
    lemma PB x y : P x => P y => P (TRL.( - ) x y).
    proof. by move: x y; apply/ZModTStr.subzmodB/subzmodP. qed.
  
    lemma PMz x n : P x => P (TRL.intmul x n).
    proof. by move: x n; apply/ZModTStr.subzmodMz/subzmodP. qed.
  
    lemma P_mem_orbit : forall x y , ZModTStr.orbit x y => P x => P y.
    proof. by apply/ZModTStr.subzmod_mem_orbit/subzmodP. qed.
  
    lemma P_mem_orbit_list : forall x y , y \in ZModTStr.orbit_list x => P x => P y.
    proof. by apply/ZModTStr.subzmod_mem_orbit_list/subzmodP. qed.
  
    lemma P_eqv_orbit :
      forall x y z ,
        ZModTStr.eqv_orbit x y z =>
        P x =>
        P y <=> P z.
    proof. by apply/ZModTStr.subzmod_eqv_orbit/subzmodP. qed.
  
    lemma insubd0 : insubd TRL.zeror = SRL.zeror.
    proof. by rewrite -val0 valKd. qed.
  
    lemma insubdD x y :
      P x =>
      P y =>
      insubd (TRL.( + ) x y) =
      SRL.( + ) (insubd x) (insubd y).
    proof.
      move=> Px Py; apply/val_inj; rewrite valD !val_insubd //.
      by rewrite Px Py PD.
    qed.
  
    lemma insubdN x :
      P x =>
      insubd (TRL.([-]) x) =
      SRL.([-]) (insubd x).
    proof.
      move=> Px; apply/val_inj; rewrite valN !val_insubd //.
      by rewrite Px PN.
    qed.
  
    lemma insubdB x y :
      P x =>
      P y =>
      insubd (TRL.( - ) x y) =
      SRL.( - ) (insubd x) (insubd y).
    proof.
      move=> Px Py; apply/val_inj; rewrite valB !val_insubd //.
      by rewrite Px Py PB.
    qed.
  
    lemma insubdMz x n :
      P x =>
      insubd (TRL.intmul x n) =
      SRL.intmul (insubd x) n.
    proof.
      move=> Px; apply/val_inj; rewrite valMz !val_insubd //.
      by rewrite Px PMz.
    qed.
  
    lemma insubd_order x : P x => order (insubd x) = order x.
    proof. by move=> Px; rewrite -val_order val_insubd Px. qed.
  
    lemma insubd_orbit x y : P x => P y => orbit (insubd x) (insubd y) = orbit x y.
    proof. by move=> Px Py; rewrite -val_orbit !val_insubd Px Py. qed.
  
    lemma insubd_orbit_list x : P x => orbit_list (insubd x) = map insubd (orbit_list x).
    proof.
      move=> Px; apply/(inj_map _ val_inj); rewrite -val_orbit_list val_insubd Px /=.
      rewrite -map_comp -{1}(map_id (orbit_list x)) -eq_in_map => y.
      rewrite /idfun /(\o) /= val_insubd => memy.
      by move/(_ _ _ memy Px): P_mem_orbit_list => ->.
    qed.
  
    lemma insubd_eqv_orbit x y z :
      P x =>
      P y =>
      P z =>
      eqv_orbit (insubd x) (insubd y) (insubd z) =
      eqv_orbit x y z.
    proof. by move=> Px Py Pz; rewrite -val_eqv_orbit !val_insubd Px Py Pz. qed.

    lemma zmod_endo_sub f :
      (forall x , P x => P (f x)) =>
      ZModTStr.zmod_endo f =>
      ZModSStr.zmod_endo (insubd \o f \o val).
    proof.
      move=> imp_ ef; rewrite /(\o); split.
      + by rewrite /morphism_0 val0 zmod_endo0 // insubd0.
      move=> x y; rewrite valD zmod_endoD // insubdD //.
      + by apply/imp_/valP.
      by apply/imp_/valP.
    qed.

    lemma zmod_mono_endo_sub f :
      (forall x , P x => P (f x)) =>
      ZModTStr.zmod_mono_endo f =>
      ZModSStr.zmod_mono_endo (insubd \o f \o val).
    proof.
      move=> imp_ ef; split; last first.
      + by apply/zmod_endo_sub => //; apply/ZModTStr.zmod_mono_endo_endo.
      rewrite /(\o) => x y /(congr1 val); rewrite !val_insubd !imp_ ?valP //=.
      by move/(ZModTStr.zmod_mono_endo_inj _ ef)/val_inj.
    qed.
  end SZMod.
end SubZModule.

(* -------------------------------------------------------------------- *)
abstract theory SubComRing.
  type t, st.

  clone include ComRingStruct with
    type t <- t
    rename [theory] "RL"  as "TRL"
           [theory] "Str" as "TStr".

  clone include ComRingStruct with
    type t <- st
    rename [theory] "RL"  as "SRL"
           [theory] "Str" as "SStr".

  clone include ComRingMorph with
    type t1 <- st,
    type t2 <- t,
    theory RL1 <- SRL,
    theory RL2 <- TRL,
    theory ZModStr1 <- ZModSStr,
    theory ZModStr2 <- ZModTStr,
    theory CRStr1   <- CRSStr,
    theory CRStr2   <- CRTStr.

  clone include SubZModule with
    type t           <- t,
    type st          <- st,
    theory TRL       <- TRL,
    theory SRL       <- SRL,
    theory ZModTStr  <- ZModTStr,
    theory ZModSStr  <- ZModSStr,
    theory ZModMorph <- ZModMorph
    rename [theory] "TRL"  as "Gone"
           [theory] "SRL"  as "Gone"
           [theory] "TStr" as "Gone"
           [theory] "SStr" as "Gone"
           [theory] "Morph" as "Gone".

  theory SCR.
    import Sub TRL SRL ZModTStr ZModSStr CRTStr CRSStr SZMod ZModMorph CRMorph.

    axiom val1 : val SRL.oner = TRL.oner.
  
    axiom valM x y : val (SRL.( * ) x y) = TRL.( * ) (val x) (val y).

    lemma val_cr_homo : cr_homo val.
    proof. by split; [apply/val_zmod_homo|split; [apply/val1|apply/valM]]. qed.

    lemma val_cr_mono : cr_mono val.
    proof. by split; [apply/val_inj|apply/val_cr_homo]. qed.
  
    lemma valUR :
      forall x ,
        SRL.unit x =>
        TRL.unit (val x).
    proof. by apply/cr_monoUR/val_cr_mono. qed.
  
    lemma valVR :
      forall x ,
        val (SRL.invr x) =
        if SRL.unit x
        then TRL.invr (val x)
        else val x.
    proof. by apply/cr_monoVR/val_cr_mono. qed.
  
    lemma valZ :
      forall n , val (SRL.ofint n) = TRL.ofint n.
    proof. by apply/cr_monoZ/val_cr_mono. qed.
  
    lemma valXR :
      forall x n ,
        val (SRL.exp x n) =
        if unit x
        then TRL.exp (val x) n
        else TRL.exp (val x) `|n|.
    proof. by apply/cr_monoXR/val_cr_mono. qed.

    lemma eq_char :
      CRSStr.char = CRTStr.char.
    proof. by apply/(cr_mono_char _ val_cr_mono). qed.

    lemma subcrP : subcr P.
    proof.
      move: (subcr_cr_mono_subcr _ _ val_cr_mono subcrT).
      apply/eq_ind/fun_ext => y; apply/eq_iff; split=> [[x] [] <<- _|Py].
      + by apply/valP.
      by exists (insubd y); rewrite val_insubd Py.
    qed.

    lemma P1 : P TRL.oner.
    proof. by apply/CRTStr.subcr1/subcrP. qed.
  
    lemma PM x y : P x => P y => P (TRL.( * ) x y).
    proof. by move: x y; apply/CRTStr.subcrM/subcrP. qed.
  
    lemma PXR x n : P x => 0 <= n => P (TRL.exp x n).
    proof. by move: x n; apply/CRTStr.subcrXR/subcrP. qed.
  
    lemma insubd1 : insubd TRL.oner = SRL.oner.
    proof. by rewrite -val1 valKd. qed.
  
    lemma insubdM x y :
      P x =>
      P y =>
      insubd (TRL.( * ) x y) =
      SRL.( * ) (insubd x) (insubd y).
    proof.
      move=> Px Py; apply/val_inj; rewrite valM !val_insubd //.
      by rewrite Px Py PM.
    qed.
  
    lemma insubdVR x :
      P x =>
      insubd (TRL.invr x) =
      if P (TRL.invr x)
      then SRL.invr (insubd x)
      else witness.
    proof.
      move=> Px; case: (TRL.unit x)=> [ux|Nux]; last first.
      + rewrite TRL.unitout // Px /=; move: (valUR (insubd x)).
        rewrite val_insubd Px /= Nux /= => Nu_.
        by rewrite SRL.unitout.
      apply/val_inj; rewrite fun_if valVR !val_insubd Px /=.
      case: (P (TRL.invr x)) => //= P_; rewrite ifT //.
      apply/SRL.unitrP; exists (insubd (TRL.invr x)).
      by rewrite -insubdM // TRL.mulVr // insubd1.
    qed.
  
    lemma insubdXR x n :
      P x =>
      insubd (TRL.exp x n) =
      if 0 <= n \/ P (TRL.invr x)
      then SRL.exp (insubd x) n
      else witness.
    proof.
      move=> Px; case (0 <= n) => [le0n|/ltrNge] /=.
      + apply/val_inj; rewrite valXR !val_insubd Px /=.
        by rewrite PXR //= ger0_norm.
      rewrite -(IntID.opprK n); move: (-n) => {n} n /oppr_lt0 lt0n.
      rewrite SRL.exprN TRL.exprN -SRL.exprVn ?ltzW //.
      rewrite -TRL.exprVn ?ltzW //; move: (insubdVR _ Px).
      case: (P (TRL.invr x)) => //= [PV <-|NPV _].
      + apply/val_inj; rewrite valXR !val_insubd PV /=.
        by rewrite PXR ?ltzW //= gtr0_norm.
      apply/val_inj; rewrite val_insubd; rewrite ifF //.
      move: NPV; apply/implybNN => PE.
      case: (TRL.unit x) => [ux|Nux]; last by rewrite TRL.unitout.
      move: (PM _ (TRL.exp x (n - 1)) PE _).
      + by apply/PXR => //; apply/ltzS.
      rewrite (TRL.exprS (TRL.invr x) (n - 1)).
      + by apply/ltzS.
      rewrite -TRL.mulrA -TRL.exprMn.
      + by apply/ltzS.
      by rewrite TRL.mulVr // TRL.expr1z TRL.mulr1.
    qed.

    lemma cr_endo_sub f :
      (forall x , P x => P (f x)) =>
      CRTStr.cr_endo f =>
      CRSStr.cr_endo (insubd \o f \o val).
    proof.
      move=> imp_ ef; split; [|split].
      + by apply/SZMod.zmod_endo_sub => //; apply/CRTStr.cr_endo_zmod.
      + by rewrite /(\o) /morphism_0 val1 cr_endo1 // insubd1.
      move=> x y; rewrite /(\o) valM cr_endoM // insubdM //.
      + by apply/imp_/valP.
      by apply/imp_/valP.
    qed.

    lemma cr_mono_endo_sub f :
      (forall x , P x => P (f x)) =>
      CRTStr.cr_mono_endo f =>
      CRSStr.cr_mono_endo (insubd \o f \o val).
    proof.
      move=> imp_ ef; split; last first.
      + by apply/cr_endo_sub => //; apply/CRTStr.cr_mono_endo_endo.
      rewrite /(\o) => x y /(congr1 val); rewrite !val_insubd !imp_ ?valP //=.
      by move/(CRTStr.cr_mono_endo_inj _ ef)/val_inj.
    qed.
  end SCR.
end SubComRing.

(* -------------------------------------------------------------------- *)
abstract theory SubIDomain.
  type t, st.

  clone include IDomainStruct with
    type t <- t
    rename [theory] "RL"  as "TRL"
           [theory] "Str" as "TStr".

  clone include IDomainStruct with
    type t <- st
    rename [theory] "RL"  as "SRL"
           [theory] "Str" as "SStr".

  clone include IDomainMorph with
    type t1 <- st,
    type t2 <- t,
    theory RL1 <- SRL,
    theory RL2 <- TRL,
    theory ZModStr1 <- ZModSStr,
    theory ZModStr2 <- ZModTStr,
    theory CRStr1   <- CRSStr,
    theory CRStr2   <- CRTStr,
    theory IDStr1   <- IDSStr,
    theory IDStr2   <- IDTStr.

  clone include SubComRing with
    type t           <- t,
    type st          <- st,
    theory TRL       <- TRL,
    theory SRL       <- SRL,
    theory ZModTStr  <- ZModTStr,
    theory ZModSStr  <- ZModSStr,
    theory ZModMorph <- ZModMorph,
    theory CRTStr    <- CRTStr,
    theory CRSStr    <- CRSStr,
    theory CRMorph   <- CRMorph
    rename [theory] "TRL"  as "Gone"
           [theory] "SRL"  as "Gone"
           [theory] "TStr" as "Gone"
           [theory] "SStr" as "Gone"
           [theory] "Morph" as "Gone".

  theory SID.
    import Sub TRL SRL ZModTStr ZModSStr CRTStr CRSStr IDTStr IDSStr SZMod SCR.
    import ZModMorph CRMorph IDMorph.

    lemma val_frobenius :
      forall x ,
        val (IDSStr.frobenius x) = IDTStr.frobenius (val x).
    proof. by apply/cr_mono_frobenius/val_cr_mono. qed.

    lemma val_iter_frobenius_fixed :
      forall n x ,
        IDTStr.iter_frobenius_fixed n (val x) =
        IDSStr.iter_frobenius_fixed n x.
    proof. by apply/cr_mono_iter_frobenius_fixed/val_cr_mono. qed.

    lemma P_frobenius :
      forall x ,
        P x =>
        P (frobenius x).
    proof. by apply/IDTStr.subcr_frobenius/subcrP. qed.

    lemma insubd_frobenius x : P x => frobenius (insubd x) = insubd (frobenius x).
    proof.
      by move=> Px; apply/val_inj; rewrite val_frobenius !val_insubd Px P_frobenius.
    qed.
  
    lemma insubd_iter_frobenius_fixed n x :
      P x =>
      iter_frobenius_fixed n (insubd x) =
      iter_frobenius_fixed n x.
    proof.
      by move=> Px; rewrite -val_iter_frobenius_fixed val_insubd Px.
    qed.
  end SID.
end SubIDomain.

(* -------------------------------------------------------------------- *)
abstract theory SubField.
  type t, st.

  clone include FieldStruct with
    type t <- t
    rename [theory] "RL"  as "TRL"
           [theory] "Str" as "TStr".

  clone include FieldStruct with
    type t <- st
    rename [theory] "RL"  as "SRL"
           [theory] "Str" as "SStr".

  clone include FieldMorph with
    type t1 <- st,
    type t2 <- t,
    theory RL1 <- SRL,
    theory RL2 <- TRL,
    theory ZModStr1 <- ZModSStr,
    theory ZModStr2 <- ZModTStr,
    theory CRStr1   <- CRSStr,
    theory CRStr2   <- CRTStr,
    theory IDStr1   <- IDSStr,
    theory IDStr2   <- IDTStr,
    theory FStr1    <- FSStr,
    theory FStr2    <- FTStr.

  clone include SubIDomain with
    type t           <- t,
    type st          <- st,
    theory TRL       <- TRL,
    theory SRL       <- SRL,
    theory ZModTStr  <- ZModTStr,
    theory ZModSStr  <- ZModSStr,
    theory ZModMorph <- ZModMorph,
    theory CRTStr    <- CRTStr,
    theory CRSStr    <- CRSStr,
    theory CRMorph   <- CRMorph,
    theory IDTStr    <- IDTStr,
    theory IDSStr    <- IDSStr,
    theory IDMorph   <- IDMorph
    rename [theory] "TRL"      as "Gone"
           [theory] "SRL"      as "Gone"
           [theory] "ZModTStr" as "Gone"
           [theory] "ZModSStr" as "Gone"
           [theory] "CRTStr"   as "Gone"
           [theory] "CRSStr"   as "Gone"
           (*TODO: Pierre-Yves: declare rewrite not cleared.*)
           [theory] "IDTStr"   as "SubIDomainIDTStrGone"
           [theory] "IDSStr"   as "SubIDomainIDSStrGone"
           [theory] "IDStr1"   as "SubIDomainIDStr1Gone"
           [theory] "IDStr2"   as "SubIDomainIDStr2Gone"
           [theory] "Morph"    as "Gone".

  theory SFld.
    import Sub TRL SRL ZModTStr ZModSStr CRTStr CRSStr IDTStr IDSStr FTStr FSStr SZMod SCR SID.
    import ZModMorph CRMorph IDMorph FMorph.

    lemma valU :
      forall x ,
        unit (val x) = unit x.
    proof. by apply/cr_monoU/val_cr_mono. qed.
  
    lemma valV :
      morphism_1 val SRL.invr TRL.invr.
    proof. by apply/cr_monoV/val_cr_mono. qed.
  
    lemma valX :
      forall x n ,
        val (SRL.exp x n) =
        TRL.exp (val x) n.
    proof. by apply/cr_monoX/val_cr_mono. qed.

    lemma subfP : subf P.
    proof.
      move: (subf_cr_mono_subf _ _ val_cr_mono subfT).
      apply/eq_ind/fun_ext => y; apply/eq_iff; split=> [[x] [] <<- _|Py].
      + by apply/valP.
      by exists (insubd y); rewrite val_insubd Py.
    qed.

    lemma PV : forall x , P x => P (invr x).
    proof. by apply/FTStr.subfV/subfP. qed.

    lemma PX : forall x n , P x => P (TRL.exp x n).
    proof. by apply/FTStr.subfX/subfP. qed.

    lemma insubdU x :
      P x =>
      unit (insubd x) = unit x.
    proof.
      by move=> Px; rewrite -valU val_insubd Px.
    qed.

    lemma insubdV x :
      P x =>
      insubd (TRL.invr x) =
      SRL.invr (insubd x).
    proof.
      move=> Px; case (x = TRL.zeror) => [->>|neqx0].
      + by rewrite TRL.invr0 insubd0 SRL.invr0.
      by rewrite insubdVR // PV.
    qed.
  
    lemma insubdX x n :
      P x =>
      insubd (TRL.exp x n) =
      SRL.exp (insubd x) n.
    proof.
      move=> Px; case (x = TRL.zeror) => [->>|neqx0].
      + by rewrite TRL.expr0z insubd0 SRL.expr0z fun_if insubd1 insubd0.
      by rewrite insubdXR // PV.
    qed.
  end SFld.
end SubField.


(* ==================================================================== *)
abstract theory SubZModulePred.
  type t, st.

  clone include ZModuleStruct with
    type t <- t
    rename [theory] "RL"  as "TRL"
           [theory] "Str" as "TStr".

  clone import Subtype as Sub with
    type T  <= t ,
    type sT <= st.

  axiom subzmodP : ZModTStr.subzmod P.

  clone include SubZModule with
    type t          <- t,
    type st         <- st,
    theory TRL      <- TRL,
    op SRL.zeror    <= insubd TRL.zeror,
    op SRL.( + )    <= (fun x y => insubd (TRL.( + ) (val x) (val y))),
    op SRL.([-])    <= (fun x => insubd (TRL.([-]) (val x))),
    theory ZModTStr <- ZModTStr,
    theory Sub      <- Sub
    rename [theory] "TRL"  as "Gone"
           [theory] "TStr" as "Gone"
           [theory] "Sub"  as "Gone"
  proof *.

  realize SRL.addrA.
  proof.
    move=> x y z; rewrite /( + ); apply/val_inj.
    rewrite !val_insubd (ZModTStr.subzmodD _ subzmodP (val x) (val y)) ?valP //=.
    rewrite (ZModTStr.subzmodD _ subzmodP (val y) (val z)) ?valP //=.
    by rewrite TRL.addrA.
  qed.

  realize SRL.addrC.
  proof.
    move=> x y; rewrite /( + ); apply/val_inj.
    rewrite !val_insubd !(ZModTStr.subzmodD _ subzmodP) ?valP //=.
    by rewrite TRL.addrC.
  qed.

  realize SRL.add0r.
  proof.
    move=> x; rewrite /zeror /( + ); apply/val_inj.
    by rewrite !val_insubd (ZModTStr.subzmod0 _ subzmodP) /= TRL.add0r valP.
  qed.

  realize SRL.addNr.
  proof.
    move=> x; rewrite /zeror /( + ) /([-]); apply/val_inj; rewrite !val_insubd.
    by rewrite (ZModTStr.subzmodN _ subzmodP) ?valP //= TRL.addNr (ZModTStr.subzmod0 _ subzmodP).
  qed.

  realize SZMod.val0.
  proof. by rewrite /zeror /morphism_0 val_insubd (ZModTStr.subzmod0 _ subzmodP). qed.

  realize SZMod.valD.
  proof.
    move=> x y; rewrite /( + ) val_insubd.
    by rewrite (ZModTStr.subzmodD _ subzmodP) // valP.
  qed.
end SubZModulePred.

(* -------------------------------------------------------------------- *)
abstract theory SubComRingPred.
  type t, st.

  clone include ComRingStruct with
    type t <- t
    rename [theory] "RL"  as "TRL"
           [theory] "Str" as "TStr".

  clone import Subtype as Sub with
    type T  <= t ,
    type sT <= st.

  axiom subcrP : CRTStr.subcr P.

  clone include SubZModulePred with
    type t          <- t,
    type st         <- st,
    theory TRL      <- TRL,
    theory ZModTStr <- ZModTStr,
    theory Sub      <- Sub
    rename [theory] "TRL"  as "Gone"
           [theory] "TStr" as "Gone"
           [theory] "SRL"  as "SubZModulePredSRL"
           [theory] "Sub"  as "Gone"
  proof *.

  realize subzmodP.
  proof. by apply/CRTStr.subcr_zmod/subcrP. qed.

  clear [SubZModulePredSRL.AddMonoid.* SubZModulePredSRL.*].

  import Sub TRL ZModTStr ZModSStr CRTStr SZMod.

  clone include SubComRing with
    type t           <- t,
    type st          <- st,
    theory TRL       <- TRL,
    op SRL.zeror     <= insubd TRL.zeror,
    op SRL.( + )     <= (fun x y => insubd (TRL.( + ) (val x) (val y))),
    op SRL.([-])     <= (fun x => insubd (TRL.([-]) (val x))),
    op SRL.oner      <= insubd TRL.oner,
    op SRL.( * )     <= (fun x y => insubd (TRL.( * ) (val x) (val y))),
    pred SRL.unit    <= (fun x => exists y , TRL.( * ) (val y) (val x) = TRL.oner),
    op SRL.invr      <= (fun x => if (exists y , TRL.( * ) (val y) (val x) = TRL.oner)
                                 then insubd (TRL.invr (val x))
                                 else x),
    theory ZModTStr  <- ZModTStr,
    theory CRTStr    <- CRTStr,
    theory ZModSStr  <- ZModSStr,
    theory SZMod     <- SZMod,
    theory ZModMorph <- ZModMorph,
    theory Sub       <- Sub
    rename [theory] "TRL"       as "Gone"
           [theory] "TStr"      as "Gone"
           [theory] "ZModSStr"  as "Gone"
           [theory] "SZMod"     as "Gone"
           [theory] "ZModMorph" as "Gone"
           [theory] "Sub"       as "Gone"
  proof *.

  realize SRL.addrA by exact SubZModulePredSRL.addrA.
  realize SRL.addrC by exact SubZModulePredSRL.addrC.
  realize SRL.add0r by exact SubZModulePredSRL.add0r.
  realize SRL.addNr by exact SubZModulePredSRL.addNr.

  realize SRL.oner_neq0.
  proof.
    apply/negP; rewrite /zeror /oner; move/(congr1 val).
    by rewrite !val_insubd SZMod.P0 (CRTStr.subcr1 _ subcrP) /= TRL.oner_neq0.
  qed.

  realize SRL.mulrA.
  proof.
    move=> x y z; rewrite /( + ); apply/val_inj.
    rewrite !val_insubd (CRTStr.subcrM _ subcrP (val x) (val y)) ?valP //=.
    rewrite (CRTStr.subcrM _ subcrP (val y) (val z)) ?valP //=.
    by rewrite TRL.mulrA.
  qed.

  realize SRL.mulrC.
  proof.
    move=> x y; rewrite /( + ); apply/val_inj.
    rewrite !val_insubd !(CRTStr.subcrM _ subcrP) ?valP //=.
    by rewrite TRL.mulrC.
  qed.

  realize SRL.mul1r.
  proof.
    move=> x; rewrite /zeror /( + ); apply/val_inj.
    by rewrite !val_insubd (CRTStr.subcr1 _ subcrP) /= TRL.mul1r valP.
  qed.

  realize SRL.mulrDl.
  proof.
    move=> x y z; rewrite /( + ) /( * ); apply/val_inj.
    rewrite !val_insubd (CRTStr.subcrD _ subcrP (val x) (val y)) ?valP //=.
    rewrite (CRTStr.subcrM _ subcrP (val x) (val z)) ?valP //=.
    rewrite (CRTStr.subcrM _ subcrP (val y) (val z)) ?valP //=.
    rewrite (CRTStr.subcrM _ subcrP _ (val z)) ?valP //=.
    + by rewrite (CRTStr.subcrD _ subcrP) // valP.
    rewrite (CRTStr.subcrD _ subcrP) ?(CRTStr.subcrM _ subcrP) ?valP //=.
    by rewrite TRL.mulrDl.
  qed.

  realize SRL.mulVr.
  proof.
    move=> x ux; rewrite /oner /( * ) /invr; apply/val_inj.
    rewrite ux /= !val_insubd; case: ux => y eq_.
    move: (mulVr (val x) _); [by apply/unitrP; exists (val y)|].
    rewrite (CRTStr.subcr1 _ subcrP) /=; move: (eq_) => <- eq__.
    move: (mulIr (val x) _ _ _ eq__); [by apply/unitrP; exists (val y)|].
    by move=> {eq__} ->; rewrite valP /= eq_ (CRTStr.subcr1 _ subcrP).
  qed.

  realize SRL.unitP.
  proof.
    move=> x y /(congr1 val); rewrite !val_insubd.
    rewrite (CRTStr.subcr1 _ subcrP) (CRTStr.subcrM _ subcrP) ?valP //=.
    by move=> eq_; exists y.
  qed.

  realize SRL.unitout.
  proof. by move=> x Nux; rewrite Nux. qed.

  realize SCR.val1.
  proof. by rewrite val_insubd (CRTStr.subcr1 _ subcrP). qed.

  realize SCR.valM.
  proof.
    move=> x y; rewrite /( * ) val_insubd.
    by rewrite (CRTStr.subcrM _ subcrP) // valP.
  qed.
end SubComRingPred.

(* -------------------------------------------------------------------- *)
abstract theory SubIDomainPred.
type t, st.

  clone include IDomainStruct with
    type t <- t
    rename [theory] "RL"  as "TRL"
           [theory] "Str" as "TStr".

  clone include SubComRingPred with
    type t          <- t,
    type st         <- st,
    theory TRL      <- TRL,
    theory ZModTStr <- ZModTStr,
    theory CRTStr   <- CRTStr
    rename [theory] "TRL"  as "Gone"
           [theory] "TStr" as "Gone"
           [theory] "SRL"  as "SubComRingPredSRL".

  clear [SubComRingPredSRL.AddMonoid.* SubComRingPredSRL.MulMonoid.* SubComRingPredSRL.*].

  import Sub TRL ZModTStr ZModSStr CRTStr CRSStr IDTStr SZMod SCR.

  clone include SubIDomain with
    type t           <- t,
    type st          <- st,
    theory TRL       <- TRL,
    op SRL.zeror     <= insubd TRL.zeror,
    op SRL.( + )     <= (fun x y => insubd (TRL.( + ) (val x) (val y))),
    op SRL.([-])     <= (fun x => insubd (TRL.([-]) (val x))),
    op SRL.oner      <= insubd TRL.oner,
    op SRL.( * )     <= (fun x y => insubd (TRL.( * ) (val x) (val y))),
    pred SRL.unit    <= (fun x => exists y , TRL.( * ) (val y) (val x) = TRL.oner),
    op SRL.invr      <= (fun x => if (exists y , TRL.( * ) (val y) (val x) = TRL.oner)
                                 then insubd (TRL.invr (val x))
                                 else x),
    theory ZModTStr  <- ZModTStr,
    theory CRTStr    <- CRTStr,
    theory IDTStr    <- IDTStr,
    theory ZModSStr  <- ZModSStr,
    theory CRSStr    <- CRSStr,
    theory SZMod     <- SZMod,
    theory SCR       <- SCR,
    theory ZModMorph <- ZModMorph,
    theory CRMorph   <- CRMorph,
    theory Sub       <- Sub
    rename [theory] "TRL"       as "Gone"
           [theory] "ZModTStr"  as "Gone"
           [theory] "CRTStr"    as "Gone"
           [theory] "IDTStr"    as "SubIDomainPredIDTStrGone"
           [theory] "ZModSStr"  as "Gone"
           [theory] "CRSStr"    as "Gone"
           [theory] "SZMod"     as "Gone"
           [theory] "SCR"       as "Gone"
           [theory] "ZModMorph" as "Gone"
           [theory] "CRMorph"   as "Gone"
           [theory] "Sub"       as "Gone"
  proof SRL.*.

  realize SRL.addrA     by exact SubComRingPredSRL.addrA.
  realize SRL.addrC     by exact SubComRingPredSRL.addrC.
  realize SRL.add0r     by exact SubComRingPredSRL.add0r.
  realize SRL.addNr     by exact SubComRingPredSRL.addNr.
  realize SRL.oner_neq0 by exact SubComRingPredSRL.oner_neq0.
  realize SRL.mulrA     by exact SubComRingPredSRL.mulrA.
  realize SRL.mulrC     by exact SubComRingPredSRL.mulrC.
  realize SRL.mul1r     by exact SubComRingPredSRL.mul1r.
  realize SRL.mulrDl    by exact SubComRingPredSRL.mulrDl.
  realize SRL.mulVr     by exact SubComRingPredSRL.mulVr.
  realize SRL.unitP     by exact SubComRingPredSRL.unitP.
  realize SRL.unitout   by exact SubComRingPredSRL.unitout.

  realize SRL.mulf_eq0.
  proof.
    move=> x y; split; [|case=> ->>]; first last.
    + apply/val_inj; rewrite !val_insubd (CRTStr.subcr0 _ subcrP) /=.
      by rewrite TRL.mul0r (CRTStr.subcr0 _ subcrP).
    + apply/val_inj; rewrite !val_insubd (CRTStr.subcr0 _ subcrP) /=.
      by rewrite TRL.mulr0 (CRTStr.subcr0 _ subcrP).
    move/(congr1 val); rewrite !val_insubd (CRTStr.subcr0 _ subcrP) /=.
    rewrite (CRTStr.subcrM _ subcrP) ?valP //= TRL.mulf_eq0.
    by case=> /(congr1 insubd); rewrite valKd => ->.
  qed.
end SubIDomainPred.

(* -------------------------------------------------------------------- *)
abstract theory SubFieldPred.
type t, st.

  clone include FieldStruct with
    type t <- t
    rename [theory] "RL"  as "TRL"
           [theory] "Str" as "TStr".

  clone import Subtype as Sub with
    type T  <= t ,
    type sT <= st.

  axiom subfP : FTStr.subf P.

  clone include SubIDomainPred with
    type t          <- t,
    type st         <- st,
    theory TRL      <- TRL,
    theory ZModTStr <- ZModTStr,
    theory CRTStr   <- CRTStr,
    theory IDTStr   <- IDTStr,
    theory Sub      <- Sub
    rename [theory] "TRL"  as "Gone"
           [theory] "TStr" as "Gone"
           [theory] "SRL"  as "SubIDomainPredSRL"
           [theory] "Sub"  as "Gone"
  proof subcrP.

  realize subcrP.
  proof. by apply/FTStr.subf_cr/subfP. qed.

  clear [SubIDomainPredSRL.AddMonoid.* SubIDomainPredSRL.MulMonoid.* SubIDomainPredSRL.*].

  import Sub TRL ZModTStr ZModSStr CRTStr CRSStr IDTStr SZMod SCR.

  clone include SubField with
    type t           <- t,
    type st          <- st,
    theory TRL       <- TRL,
    op SRL.zeror     <= insubd TRL.zeror,
    op SRL.( + )     <= (fun x y => insubd (TRL.( + ) (val x) (val y))),
    op SRL.([-])     <= (fun x => insubd (TRL.([-]) (val x))),
    op SRL.oner      <= insubd TRL.oner,
    op SRL.( * )     <= (fun x y => insubd (TRL.( * ) (val x) (val y))),
    pred SRL.unit    <= (fun x => exists y , TRL.( * ) (val y) (val x) = TRL.oner),
    op SRL.invr      <= (fun x => if (exists y , TRL.( * ) (val y) (val x) = TRL.oner)
                                  then insubd (TRL.invr (val x))
                                  else x),
    theory ZModTStr  <- ZModTStr,
    theory CRTStr    <- CRTStr,
    theory ZModSStr  <- ZModSStr,
    theory CRSStr    <- CRSStr,
    theory IDSStr    <- IDSStr,
    theory SZMod     <- SZMod,
    theory SCR       <- SCR,
    theory SID       <- SID,
    theory ZModMorph <- ZModMorph,
    theory CRMorph   <- CRMorph,
    theory IDMorph   <- IDMorph,
    theory Sub       <- Sub
    rename [theory] "TRL"       as "Gone"
           [theory] "ZModTStr"  as "Gone"
           [theory] "CRTStr"    as "Gone"
           [theory] "IDTStr"    as "SubFieldPredIDTStrGone"
           [theory] "FTStr"     as "SubFieldPredFTStrGone"
           [theory] "ZModSStr"  as "Gone"
           [theory] "CRSStr"    as "Gone"
           [theory] "IDSStr"    as "SubFieldPredIDSStrGone"
           [theory] "IDStr1"    as "SubFieldPredIDStr1Gone"
           [theory] "IDStr2"    as "SubFieldPredIDStr2Gone"
           [theory] "FStr2"     as "SubFieldPredFStr2Gone"
           [theory] "SZMod"     as "Gone"
           [theory] "SCR"       as "Gone"
           [theory] "SID"       as "Gone"
           [theory] "ZModMorph" as "Gone"
           [theory] "CRMorph"   as "Gone"
           [theory] "IDMorph"   as "Gone"
           [theory] "Sub"       as "Gone"
  proof SRL.*.

  realize SRL.addrA     by exact SubIDomainPredSRL.addrA.
  realize SRL.addrC     by exact SubIDomainPredSRL.addrC.
  realize SRL.add0r     by exact SubIDomainPredSRL.add0r.
  realize SRL.addNr     by exact SubIDomainPredSRL.addNr.
  realize SRL.oner_neq0 by exact SubIDomainPredSRL.oner_neq0.
  realize SRL.mulrA     by exact SubIDomainPredSRL.mulrA.
  realize SRL.mulrC     by exact SubIDomainPredSRL.mulrC.
  realize SRL.mul1r     by exact SubIDomainPredSRL.mul1r.
  realize SRL.mulrDl    by exact SubIDomainPredSRL.mulrDl.
  realize SRL.mulVr     by exact SubIDomainPredSRL.mulVr.
  realize SRL.unitP     by exact SubIDomainPredSRL.unitP.
  realize SRL.unitout   by exact SubIDomainPredSRL.unitout.
  realize SRL.mulf_eq0  by exact SubIDomainPredSRL.mulf_eq0.

  realize SRL.unitfP.
  proof.
    move=> x neqx0; move: (TRL.unitfP (val x) _).
    + move: neqx0; apply/implybNN => eq_; apply/val_inj.
      by rewrite val_insubd (FTStr.subf0 _ subfP).
    case/TRL.unitrP => y eq_; exists (insubd y).
    rewrite val_insubd ifT //.
    move: (FTStr.subfV _ subfP _ (valP x)).
    have ->//: invr (val x) = y.
    apply/(TRL.mulIr (val x) _).
    + apply/unitfE; move: neqx0; apply/implybNN => eq__; apply/val_inj.
      by rewrite val_insubd (FTStr.subf0 _ subfP).
    rewrite eq_ mulVr //; apply/unitfE; move: neqx0.
    apply/implybNN => eq__; apply/val_inj.
    by rewrite val_insubd (FTStr.subf0 _ subfP).
  qed.
end SubFieldPred.


(* ==================================================================== *)
abstract theory SubIDomainFrobenius.
  type t, st.

  clone include IDomainStruct with
    type t <- t
    rename [theory] "RL"  as "TRL"
           [theory] "Str" as "TStr".

  import CRTStr IDTStr.

  op n : int.
  axiom prime_char : prime char.

  clone include SubIDomainPred with
    type t          <- t,
    type st         <- st,
    theory TRL      <- TRL,
    theory ZModTStr <- ZModTStr,
    theory CRTStr   <- CRTStr,
    theory IDTStr   <- IDTStr,
    pred Sub.P      <- iter_frobenius_fixed n
    rename [theory] "TRL"  as "Gone"
           [theory] "TStr" as "Gone"
  proof subcrP.

  realize subcrP.
  proof. by apply/subcr_iter_frobenius_fixed/prime_char. qed.
end SubIDomainFrobenius.

(* -------------------------------------------------------------------- *)
abstract theory SubFieldFrobenius.
  type t, st.

  clone include FieldStruct with
    type t <- t
    rename [theory] "RL"  as "TRL"
           [theory] "Str" as "TStr".

  import CRTStr IDTStr.

  op n : int.
  axiom prime_char : prime char.

  clone include SubFieldPred with
    type t          <- t,
    type st         <- st,
    theory TRL      <- TRL,
    theory ZModTStr <- ZModTStr,
    theory CRTStr   <- CRTStr,
    theory IDTStr   <- IDTStr,
    theory FTStr    <- FTStr,
    pred Sub.P      <- iter_frobenius_fixed n
    rename [theory] "TRL"    as "Gone"
           [theory] "TStr"   as "Gone"
           [theory] "IDGone" as "SubFieldFrobeniusIDGone"
  (*TODO: pierre-Yves: I can ask to re prove a lemma?*)
  proof (*subcrP,*) subfP.

  realize subfP.
  proof. by apply/FTStr.subf_iter_frobenius_fixed/prime_char. qed.
end SubFieldFrobenius.

