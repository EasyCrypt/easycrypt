(* -------------------------------------------------------------------- *)
require import AllCore List Ring Int IntDiv Bigalg RingStruct.
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

  clone import Subtype as Sub with
    type T  <= t ,
    type sT <= st.

  theory SZMod.
    import Sub TRL SRL ZModTStr ZModSStr.

    axiom val0 : val SRL.zeror = TRL.zeror.
  
    axiom valD x y : val (SRL.( + ) x y) = TRL.( + ) (val x) (val y).
  
    lemma valN x : val (SRL.([-]) x) = TRL.([-]) (val x).
    proof. by apply/(TRL.addrI (val x)); rewrite -valD SRL.subrr TRL.subrr val0. qed.
  
    lemma valB x y : val (SRL.( - ) x y) = TRL.( - ) (val x) (val y).
    proof. by rewrite valD valN. qed.
  
    lemma valMz x n : val (SRL.intmul x n) = TRL.intmul (val x) n.
    proof.
      wlog: n / 0 <= n => [wlogn|].
      + case (0 <= n) => [|/ltrNge/ltzW/ler_opp2/=] /wlogn // => {wlogn}.
        by rewrite SRL.mulrNz TRL.mulrNz valN => /TRL.oppr_inj.
      elim: n => [|n le0n IHn]; [by rewrite SRL.mulr0z TRL.mulr0z val0|].
      by rewrite SRL.mulrSz TRL.mulrSz -IHn valD.
    qed.

    lemma subzmodP : ZModTStr.is_subzmod P.
    proof.
      do!split.
      + by rewrite -val0 valP.
      + move=> x y Px Py; move: (val_insubd x) (val_insubd y).
        by rewrite Px Py /= => <- <-; rewrite -valD valP.
      move=> x Px; move: (val_insubd x).
      by rewrite Px /= => <-; rewrite -valN valP.
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
  
    lemma val_order x : order (val x) = order x.
    proof.
      rewrite /order; apply/IntMin.eq_argmin => i le0i /=.
      rewrite /idfun /= -valMz -val0; apply/andb_id2l => lt0i.
      by apply/eq_iff; split=> [|->] //; apply/val_inj.
    qed.
  
    lemma val_orbit x y : orbit (val x) (val y) = orbit x y.
    proof.
      apply/eq_iff/exists_eq => n /=; apply/eq_iff.
      by rewrite -valMz; split=> [|->] // /val_inj.
    qed.
  
    lemma val_orbit_list x : orbit_list (val x) = map val (orbit_list x).
    proof.
      rewrite map_mkseq -val_order; apply/eq_in_mkseq.
      by move=> i _ ; rewrite /(\o) /= valMz.
    qed.
  
    lemma val_eqv_orbit x y z : eqv_orbit (val x) (val y) (val z) = eqv_orbit x y z.
    proof. by rewrite /eqv_orbit -valB val_orbit. qed.
  
    lemma P_orbit_list x : P x => all P (orbit_list x).
    proof.
      case/ler_eqVlt: (ZModTStr.ge0_order x) => [|lt0_ Px].
      + by rewrite -size_orbit_list eq_sym size_eq0 => ->.
      apply/allP => y; rewrite -orbit_listP // => -[n] ->>.
      by apply/PMz.
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
      by move/(_ _ Px)/allP/(_ _ memy): P_orbit_list => ->.
    qed.
  
    lemma insubd_eqv_orbit x y z :
      P x =>
      P y =>
      P z =>
      eqv_orbit (insubd x) (insubd y) (insubd z) =
      eqv_orbit x y z.
    proof. by move=> Px Py Pz; rewrite -val_eqv_orbit !val_insubd Px Py Pz. qed.
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

  clone include SubZModule with
    type t          <- t,
    type st         <- st,
    theory TRL      <- TRL,
    theory SRL      <- SRL,
    theory ZModTStr <- ZModTStr,
    theory ZModSStr <- ZModSStr
    rename [theory] "TRL"  as "Gone"
           [theory] "SRL"  as "Gone"
           [theory] "TStr" as "Gone"
           [theory] "SStr" as "Gone".

  theory SCR.
    import Sub TRL SRL ZModTStr ZModSStr CRTStr CRSStr SZMod.

    axiom val1 : val SRL.oner = TRL.oner.
  
    axiom valM x y : val (SRL.( * ) x y) = TRL.( * ) (val x) (val y).
  
    lemma valUR x : SRL.unit x => TRL.unit (val x).
    proof.
      rewrite TRL.unitrP SRL.unitrP -val1 => -[y] <-.
      by exists (val y); rewrite valM.
    qed.
  
    lemma valVR x :
      val (SRL.invr x) =
      if SRL.unit x
      then TRL.invr (val x)
      else val x.
    proof.
      case: (SRL.unit x) => [ux|Nux].
      + apply/(TRL.mulIr _ (valUR _ ux)).
        rewrite -valM SRL.mulVr // TRL.mulVr ?val1 //.
        by apply/valUR.
      by rewrite SRL.unitout.
    qed.
  
    lemma valXR x n :
      val (SRL.exp x n) =
      if SRL.unit x
      then TRL.exp (val x) n
      else TRL.exp (val x) `|n|.
    proof.
      have wlogn: forall x n , 0 <= n => val (SRL.exp x n) = TRL.exp (val x) n.
      + move=> {x n} x; elim=> [|n le0n IHn]; [by rewrite SRL.expr0 TRL.expr0 val1|].
        by rewrite SRL.exprS // TRL.exprS // -IHn valM.
      case (0 <= n) => [le0n|/ltrNge ltn0].
      + by rewrite wlogn // ger0_norm.
      rewrite ltr0_norm //; move: ltn0; rewrite -(IntID.opprK n).
      move: (-n) => {n} n /oppr_lt0 /=; rewrite SRL.exprN TRL.exprN.
      move=> lt0n; move/ltzW: (lt0n).
      move=> /wlogn {wlogn}; rewrite valVR => ->.
      case: (SRL.unit x) => [ux|Nux_].
      + by rewrite ifT //; apply/SRL.unitrX.
      case (n = 0) => [->> //|].
      by move/(SRL.unitrX_neq0 x); rewrite Nux_ /= => ->.
    qed.

    lemma subcrP : CRTStr.is_subcr P.
    proof.
      split; [by apply/SZMod.subzmodP|split].
      + by rewrite -val1 valP.
      move=> x y Px Py; move: (val_insubd x) (val_insubd y).
      by rewrite Px Py /= => <- <-; rewrite -valM valP.
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
  
    lemma eq_char : CRTStr.char = CRSStr.char.
    proof. by rewrite /char -val_order val1. qed.
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

  clone include SubComRing with
    type t          <- t,
    type st         <- st,
    theory TRL      <- TRL,
    theory SRL      <- SRL,
    theory ZModTStr <- ZModTStr,
    theory ZModSStr <- ZModSStr,
    theory CRTStr   <- CRTStr,
    theory CRSStr   <- CRSStr
    rename [theory] "TRL"  as "Gone"
           [theory] "SRL"  as "Gone"
           [theory] "TStr" as "Gone"
           [theory] "SStr" as "Gone".

  theory SID.
    import Sub TRL SRL ZModTStr ZModSStr CRTStr CRSStr IDTStr IDSStr SZMod SCR.

    lemma val_frobenius x : frobenius (val x) = val (frobenius x).
    proof. by rewrite /frobenius valXR eq_char ger0_norm // ge0_char. qed.
  
    lemma val_iter_frobenius_fixed n x :
      iter_frobenius_fixed n (val x) =
      iter_frobenius_fixed n x.
    proof.
      rewrite /iter_frobenius_fixed.
      have ->: iter n IDTStr.frobenius (val x) = val (iter n IDSStr.frobenius x).
      + case (0 <= n) => [|/ltrNge/ltzW len0]; [|by rewrite !iter0].
        by elim: n => [|n le0n IHn]; [rewrite !iter0|rewrite !iterS // IHn val_frobenius].
      by apply/eq_iff; split=> [|->] //; apply/val_inj.
    qed.
  
    lemma P_frobenius x : P x => P (frobenius x).
    proof. by move=> Px; rewrite /frobenius PXR // ge0_char. qed.
  
    lemma insubd_frobenius x : P x => frobenius (insubd x) = insubd (frobenius x).
    proof.
      by move=> Px; apply/val_inj; rewrite -val_frobenius !val_insubd Px P_frobenius.
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

  clone include SubIDomain with
    type t          <- t,
    type st         <- st,
    theory TRL      <- TRL,
    theory SRL      <- SRL,
    theory ZModTStr <- ZModTStr,
    theory ZModSStr <- ZModSStr,
    theory CRTStr   <- CRTStr,
    theory CRSStr   <- CRSStr,
    theory IDTStr   <- IDTStr,
    theory IDSStr   <- IDSStr
    rename [theory] "TRL"  as "Gone"
           [theory] "SRL"  as "Gone"
           [theory] "ZModTStr" as "Gone"
           [theory] "ZModSStr" as "Gone"
           [theory] "CRTStr" as "Gone"
           [theory] "CRSStr" as "Gone"
           (*TODO: Pierre-Yves: declare rewrite not cleared.*)
           [theory] "IDTStr" as "SubIDomainIDTStrGone"
           [theory] "IDSStr" as "SubIDomainIDSStrGone".

  theory SF.
    import Sub TRL SRL ZModTStr ZModSStr CRTStr CRSStr IDTStr IDSStr FTStr FSStr SZMod SCR SID.
  
    lemma valU x : TRL.unit (val x) = SRL.unit x.
    proof.
      case (x = SRL.zeror) => [->>|neqx0].
      + by rewrite val0 SRL.unitr0 TRL.unitr0.
      rewrite SRL.unitfP // eqT; apply/TRL.unitfP.
      by move: neqx0; rewrite -val0; apply/implybNN/val_inj.
    qed.
  
    lemma valV x :
      val (SRL.invr x) =
      TRL.invr (val x).
    proof.
      case (x = SRL.zeror) => [->>|neqx0].
      + by rewrite SRL.invr0 val0 TRL.invr0.
      by rewrite valVR SRL.unitfP.
    qed.
  
    lemma valX x n :
      val (SRL.exp x n) =
      TRL.exp (val x) n.
    proof.
      case (x = SRL.zeror) => [->>|neqx0].
      + by rewrite SRL.expr0z val0 TRL.expr0z fun_if val1 val0.
      by rewrite valXR SRL.unitfP.
    qed.

    lemma subfP : FTStr.is_subf P.
    proof.
      split; [by apply/SCR.subcrP|].
      move=> x Px; move: (val_insubd x).
      by rewrite Px /= => <-; rewrite -valV valP.
    qed.
  
    lemma PV x : P x => P (TRL.invr x).
    proof. by move: x; apply/FTStr.subfV/subfP. qed.
  
    lemma PX x n : P x => P (TRL.exp x n).
    proof. by move: x n; apply/FTStr.subfX/subfP. qed.
  
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
  end SF.
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

  axiom subzmodP : ZModTStr.is_subzmod P.

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
  proof. by rewrite /zeror val_insubd (ZModTStr.subzmod0 _ subzmodP). qed.

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

  axiom subcrP : CRTStr.is_subcr P.

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
    type t          <- t,
    type st         <- st,
    theory TRL      <- TRL,
    op SRL.zeror    <= insubd TRL.zeror,
    op SRL.( + )    <= (fun x y => insubd (TRL.( + ) (val x) (val y))),
    op SRL.([-])    <= (fun x => insubd (TRL.([-]) (val x))),
    op SRL.oner     <= insubd TRL.oner,
    op SRL.( * )    <= (fun x y => insubd (TRL.( * ) (val x) (val y))),
    pred SRL.unit   <= (fun x => exists y , TRL.( * ) (val y) (val x) = TRL.oner),
    op SRL.invr     <= (fun x => if (exists y , TRL.( * ) (val y) (val x) = TRL.oner)
                                 then insubd (TRL.invr (val x))
                                 else x),
    theory ZModTStr <- ZModTStr,
    theory CRTStr   <- CRTStr,
    theory ZModSStr <- ZModSStr,
    theory SZMod    <- SZMod,
    theory Sub      <- Sub
    rename [theory] "TRL"      as "Gone"
           [theory] "TStr"     as "Gone"
           [theory] "ZModSStr" as "Gone"
           [theory] "SZMod"    as "Gone"
           [theory] "Sub"      as "Gone"
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
    type t          <- t,
    type st         <- st,
    theory TRL      <- TRL,
    op SRL.zeror    <= insubd TRL.zeror,
    op SRL.( + )    <= (fun x y => insubd (TRL.( + ) (val x) (val y))),
    op SRL.([-])    <= (fun x => insubd (TRL.([-]) (val x))),
    op SRL.oner     <= insubd TRL.oner,
    op SRL.( * )    <= (fun x y => insubd (TRL.( * ) (val x) (val y))),
    pred SRL.unit   <= (fun x => exists y , TRL.( * ) (val y) (val x) = TRL.oner),
    op SRL.invr     <= (fun x => if (exists y , TRL.( * ) (val y) (val x) = TRL.oner)
                                 then insubd (TRL.invr (val x))
                                 else x),
    theory ZModTStr <- ZModTStr,
    theory CRTStr   <- CRTStr,
    theory IDTStr   <- IDTStr,
    theory ZModSStr <- ZModSStr,
    theory CRSStr   <- CRSStr,
    theory SZMod    <- SZMod,
    theory SCR      <- SCR,
    theory Sub      <- Sub
    rename [theory] "TRL"      as "Gone"
           [theory] "ZModTStr" as "Gone"
           [theory] "CRTStr"   as "Gone"
           [theory] "IDTStr"   as "SubIDomainPredIDTStrGone"
           [theory] "ZModSStr" as "Gone"
           [theory] "CRSStr"   as "Gone"
           [theory] "SZMod"    as "Gone"
           [theory] "SCR"      as "Gone"
           [theory] "Sub"      as "Gone"
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

  axiom subfP : FTStr.is_subf P.

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
    type t          <- t,
    type st         <- st,
    theory TRL      <- TRL,
    op SRL.zeror    <= insubd TRL.zeror,
    op SRL.( + )    <= (fun x y => insubd (TRL.( + ) (val x) (val y))),
    op SRL.([-])    <= (fun x => insubd (TRL.([-]) (val x))),
    op SRL.oner     <= insubd TRL.oner,
    op SRL.( * )    <= (fun x y => insubd (TRL.( * ) (val x) (val y))),
    pred SRL.unit   <= (fun x => exists y , TRL.( * ) (val y) (val x) = TRL.oner),
    op SRL.invr     <= (fun x => if (exists y , TRL.( * ) (val y) (val x) = TRL.oner)
                                 then insubd (TRL.invr (val x))
                                 else x),
    theory ZModTStr <- ZModTStr,
    theory CRTStr   <- CRTStr,
    theory ZModSStr <- ZModSStr,
    theory CRSStr   <- CRSStr,
    theory IDSStr   <- IDSStr,
    theory SZMod    <- SZMod,
    theory SCR      <- SCR,
    theory SID      <- SID,
    theory Sub      <- Sub
    rename [theory] "TRL"      as "Gone"
           [theory] "ZModTStr" as "Gone"
           [theory] "CRTStr"   as "Gone"
           [theory] "IDTStr"   as "SubFieldPredIDTStrGone"
           [theory] "FTStr"    as "SubFieldPredFTStrGone"
           [theory] "ZModSStr" as "Gone"
           [theory] "CRSStr"   as "Gone"
           [theory] "IDSStr"   as "SubFieldPredIDSStrGone"
           [theory] "SZMod"    as "Gone"
           [theory] "SCR"      as "Gone"
           [theory] "SID"      as "Gone"
           [theory] "Sub"      as "Gone"
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

print SubFieldPred.


(* ==================================================================== *)
theory SubIDomainFrobenius.
  type t, st.

  op n : int.
  axiom le0n : 0 <= n.

  clone include IDomainStruct with
    type t <- t
    rename [theory] "RL"  as "TRL"
           [theory] "Str" as "TStr".

  import CRTStr IDTStr.

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
  proof.
    admit.
  qed.
end SubIDomainFrobenius.
