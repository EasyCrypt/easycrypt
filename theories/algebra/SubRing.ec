(* -------------------------------------------------------------------- *)
require import AllCore List Ring Int IntDiv Bigalg RingStruct.
require (*--*) Subtype.
(*---*) import StdOrder.IntOrder.



(* ==================================================================== *)
abstract theory SubZModule.
  type t, st.

  clone import ZModuleStruct as RStr with
    type t <= t.

  clone import ZModuleStruct as SRStr with
    type t <= st.

  clone import Subtype as Sub with
    type T  <= t ,
    type sT <= st.

  axiom val0 : val SRStr.R.zeror = RStr.R.zeror.

  axiom valD x y : val (SRStr.R.( + ) x y) = RStr.R.( + ) (val x) (val y).

  lemma valN x : val (SRStr.R.([-]) x) = RStr.R.([-]) (val x).
  proof. by apply/(RStr.R.addrI (val x)); rewrite -valD SRStr.R.subrr RStr.R.subrr val0. qed.

  lemma valB x y : val (SRStr.R.( - ) x y) = RStr.R.( - ) (val x) (val y).
  proof. by rewrite valD valN. qed.

  lemma valMz x n : val (SRStr.R.intmul x n) = RStr.R.intmul (val x) n.
  proof.
    wlog: n / 0 <= n => [wlogn|].
    + case (0 <= n) => [|/ltrNge/ltzW/ler_opp2/=] /wlogn // => {wlogn}.
      by rewrite SRStr.R.mulrNz RStr.R.mulrNz valN => /RStr.R.oppr_inj.
    elim: n => [|n le0n IHn]; [by rewrite SRStr.R.mulr0z RStr.R.mulr0z val0|].
    by rewrite SRStr.R.mulrSz RStr.R.mulrSz -IHn valD.
  qed.

  lemma P0 : P RStr.R.zeror.
  proof. by rewrite -val0 valP. qed.

  lemma PD x y : P x => P y => P (RStr.R.( + ) x y).
  proof.
    move=> Px Py; move: (val_insubd x) (val_insubd y).
    by rewrite Px Py /= => <- <-; rewrite -valD valP.
  qed.

  lemma PN x : P x => P (RStr.R.([-]) x).
  proof.
    move=> Px; move: (val_insubd x).
    by rewrite Px /= => <-; rewrite -valN valP.
  qed.

  lemma PB x y : P x => P y => P (RStr.R.( - ) x y).
  proof. by move=> Px Py; apply/PD/PN. qed.

  lemma PMz x n : P x => P (RStr.R.intmul x n).
  proof.
    move=> Px; move: (val_insubd x).
    by rewrite Px /= => <-; rewrite -valMz valP.
  qed.

  lemma insubd0 : insubd RStr.R.zeror = SRStr.R.zeror.
  proof. by rewrite -val0 valKd. qed.

  lemma insubdD x y :
    P x =>
    P y =>
    insubd (RStr.R.( + ) x y) =
    SRStr.R.( + ) (insubd x) (insubd y).
  proof.
    move=> Px Py; apply/val_inj; rewrite valD !val_insubd //.
    by rewrite Px Py PD.
  qed.

  lemma insubdN x :
    P x =>
    insubd (RStr.R.([-]) x) =
    SRStr.R.([-]) (insubd x).
  proof.
    move=> Px; apply/val_inj; rewrite valN !val_insubd //.
    by rewrite Px PN.
  qed.

  lemma insubdB x y :
    P x =>
    P y =>
    insubd (RStr.R.( - ) x y) =
    SRStr.R.( - ) (insubd x) (insubd y).
  proof.
    move=> Px Py; apply/val_inj; rewrite valB !val_insubd //.
    by rewrite Px Py PB.
  qed.

  lemma insubdMz x n :
    P x =>
    insubd (RStr.R.intmul x n) =
    SRStr.R.intmul (insubd x) n.
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
    case/ler_eqVlt: (RStr.ge0_order x) => [|lt0_ Px].
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
end SubZModule.

(* -------------------------------------------------------------------- *)
abstract theory SubComRing.
  type t, st.

  clone import ComRingStruct as RStr with
    type t <= t.

  clone import ComRingStruct as SRStr with
    type t <= st.

  clone include SubZModule with
    type t       <- t,
    type st      <- st,
    theory RStr  <- RStr,
    theory SRStr <- SRStr
    rename [theory] "SRStr" as "Gone"
           [theory] "RStr"  as "Gone".

  import Sub.

  axiom val1 : val SRStr.R.oner = RStr.R.oner.

  axiom valM x y : val (SRStr.R.( * ) x y) = RStr.R.( * ) (val x) (val y).

  lemma valUR x : SRStr.R.unit x => RStr.R.unit (val x).
  proof.
    rewrite RStr.R.unitrP SRStr.R.unitrP -val1 => -[y] <-.
    by exists (val y); rewrite valM.
  qed.

  lemma valVR x :
    val (SRStr.R.invr x) =
    if SRStr.R.unit x
    then RStr.R.invr (val x)
    else val x.
  proof.
    case:(SRStr.R.unit x) => [ux|Nux].
    + apply/(RStr.R.mulIr _ (valUR _ ux)).
      rewrite -valM SRStr.R.mulVr // RStr.R.mulVr ?val1 //.
      by apply/valUR.
    by rewrite SRStr.R.unitout.
  qed.

  lemma valXR x n :
    val (SRStr.R.exp x n) =
    if SRStr.R.unit x
    then RStr.R.exp (val x) n
    else RStr.R.exp (val x) `|n|.
  proof.
    have wlogn: forall x n , 0 <= n => val (SRStr.R.exp x n) = RStr.R.exp (val x) n.
    + move=> {x n} x; elim=> [|n le0n IHn]; [by rewrite SRStr.R.expr0 RStr.R.expr0 val1|].
      by rewrite SRStr.R.exprS // RStr.R.exprS // -IHn valM.
    case (0 <= n) => [le0n|/ltrNge ltn0].
    + by rewrite wlogn // ger0_norm.
    rewrite ltr0_norm //; move: ltn0; rewrite -(opprK n).
    move: (-n) => {n} n /oppr_lt0 /=; rewrite SRStr.R.exprN RStr.R.exprN.
    move=> lt0n; move/ltzW: (lt0n).
    move=> /wlogn {wlogn}; rewrite valVR => ->.
    case: (SRStr.R.unit x) => [ux|Nux_].
    + by rewrite ifT //; apply/SRStr.R.unitrX.
    case (n = 0) => [->> //|].
    by move/(SRStr.R.unitrX_neq0 x); rewrite Nux_ /= => ->.
  qed.

  lemma P1 : P RStr.R.oner.
  proof. by rewrite -val1 valP. qed.

  lemma PM x y : P x => P y => P (RStr.R.( * ) x y).
  proof.
    move=> Px Py; move: (val_insubd x) (val_insubd y).
    by rewrite Px Py /= => <- <-; rewrite -valM valP.
  qed.

  lemma PXR x n : P x => 0 <= n => P (RStr.R.exp x n).
  proof.
    move=> Px; elim: n => [|n le0n IHn].
    + by rewrite RStr.R.expr0 P1.
    by rewrite RStr.R.exprS // PM.
  qed.

  lemma insubd1 : insubd RStr.R.oner = SRStr.R.oner.
  proof. by rewrite -val1 valKd. qed.

  lemma insubdM x y :
    P x =>
    P y =>
    insubd (RStr.R.( * ) x y) =
    SRStr.R.( * ) (insubd x) (insubd y).
  proof.
    move=> Px Py; apply/val_inj; rewrite valM !val_insubd //.
    by rewrite Px Py PM.
  qed.

  lemma insubdVR x :
    P x =>
    insubd (RStr.R.invr x) =
    if P (RStr.R.invr x)
    then SRStr.R.invr (insubd x)
    else witness.
  proof.
    move=> Px; case: (RStr.R.unit x)=> [ux|Nux]; last first.
    + rewrite RStr.R.unitout // Px /=; move: (valUR (insubd x)).
      rewrite val_insubd Px /= Nux /= => Nu_.
      by rewrite SRStr.R.unitout.
    apply/val_inj; rewrite fun_if valVR !val_insubd Px /=.
    case: (P (RStr.R.invr x)) => //= P_; rewrite ifT //.
    apply/SRStr.R.unitrP; exists (insubd (RStr.R.invr x)).
    by rewrite -insubdM // RStr.R.mulVr // insubd1.
  qed.

  lemma insubdXR x n :
    P x =>
    insubd (RStr.R.exp x n) =
    if 0 <= n \/ P (RStr.R.invr x)
    then SRStr.R.exp (insubd x) n
    else witness.
  proof.
    move=> Px; case (0 <= n) => [le0n|/ltrNge] /=.
    + apply/val_inj; rewrite valXR !val_insubd Px /=.
      by rewrite PXR //= ger0_norm.
    rewrite -(opprK n); move: (-n) => {n} n /oppr_lt0 lt0n.
    rewrite SRStr.R.exprN RStr.R.exprN -SRStr.R.exprVn ?ltzW //.
    rewrite -RStr.R.exprVn ?ltzW //; move: (insubdVR _ Px).
    case: (P (RStr.R.invr x)) => //= [PV <-|NPV _].
    + apply/val_inj; rewrite valXR !val_insubd PV /=.
      by rewrite PXR ?ltzW //= gtr0_norm.
    apply/val_inj; rewrite val_insubd; rewrite ifF //.
    move: NPV; apply/implybNN => PE.
    case: (RStr.R.unit x) => [ux|Nux]; last by rewrite RStr.R.unitout.
    move: (PM _ (RStr.R.exp x (n - 1)) PE _).
    + by apply/PXR => //; apply/ltzS.
    rewrite (RStr.R.exprS (RStr.R.invr x) (n - 1)).
    + by apply/ltzS.
    rewrite -RStr.R.mulrA -RStr.R.exprMn.
    + by apply/ltzS.
    by rewrite RStr.R.mulVr // RStr.R.expr1z RStr.R.mulr1.
  qed.

  lemma eq_char : RStr.char = SRStr.char.
  proof. by rewrite /char -val_order val1. qed.
end SubComRing.

(* -------------------------------------------------------------------- *)
abstract theory SubIDomain.
  type t, st.

  clone import IDomainStruct as RStr with
    type t <= t.

  clone import IDomainStruct as SRStr with
    type t <= st.

  clone include SubComRing with
    type t       <- t,
    type st      <- st,
    theory RStr  <- RStr,
    theory SRStr <- SRStr
    rename [theory] "SRStr" as "Gone"
           [theory] "RStr"  as "Gone".

  import Sub.

  lemma val_frobenius x : frobenius (val x) = val (frobenius x).
  proof. by rewrite /frobenius valXR eq_char ger0_norm // SRStr.ge0_char. qed.

  lemma val_iter_frobenius_fixed n x :
    iter_frobenius_fixed n (val x) =
    iter_frobenius_fixed n x.
  proof.
    rewrite /iter_frobenius_fixed.
    have ->: iter n RStr.frobenius (val x) = val (iter n SRStr.frobenius x).
    + case (0 <= n) => [|/ltrNge/ltzW len0]; [|by rewrite !iter0].
      by elim: n => [|n le0n IHn]; [rewrite !iter0|rewrite !iterS // IHn val_frobenius].
    by apply/eq_iff; split=> [|->] //; apply/val_inj.
  qed.

  lemma P_frobenius x : P x => P (frobenius x).
  proof. by move=> Px; rewrite /frobenius PXR // RStr.ge0_char. qed.

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
end SubIDomain.

(* -------------------------------------------------------------------- *)
abstract theory SubField.
  type t, st.

  clone import FieldStruct as RStr with
    type t <= t.

  clone import FieldStruct as SRStr with
    type t <= st.

  clone include SubIDomain with
    type t       <- t,
    type st      <- st,
    theory RStr  <- RStr,
    theory SRStr <- SRStr
    rename [theory] "SRStr" as "SGone"
           [theory] "RStr"  as "Gone".

  import Sub.

  lemma valU x : RStr.R.unit (val x) = SRStr.R.unit x.
  proof.
    case (x = SRStr.R.zeror) => [->>|neqx0].
    + by rewrite val0 SRStr.R.unitr0 RStr.R.unitr0.
    rewrite SRStr.R.unitfP // eqT; apply/RStr.R.unitfP.
    by move: neqx0; rewrite -val0; apply/implybNN/val_inj.
  qed.

  lemma valV x :
    val (SRStr.R.invr x) =
    RStr.R.invr (val x).
  proof.
    case (x = SRStr.R.zeror) => [->>|neqx0].
    + by rewrite SRStr.R.invr0 val0 RStr.R.invr0.
    by rewrite valVR SRStr.R.unitfP.
  qed.

  lemma valX x n :
    val (SRStr.R.exp x n) =
    RStr.R.exp (val x) n.
  proof.
    case (x = SRStr.R.zeror) => [->>|neqx0].
    + by rewrite SRStr.R.expr0z val0 RStr.R.expr0z fun_if val1 val0.
    by rewrite valXR SRStr.R.unitfP.
  qed.

  lemma PV x : P x => P (RStr.R.invr x).
  proof.
    move=> Px; move: (val_insubd x).
    by rewrite Px /= => <-; rewrite -valV valP.
  qed.

  lemma PX x n : P x => P (RStr.R.exp x n).
  proof.
    move=> Px; case (0 <= n) => [le0n|/ltrNge/ltzW/ler_opp2/=].
    + by apply/PXR.
    rewrite -(opprK n); move: (-n) => {n} n /= le0n.
    by rewrite -RStr.R.exprV; apply/PXR => //; apply/PV.
  qed.

  lemma insubdV x :
    P x =>
    insubd (RStr.R.invr x) =
    SRStr.R.invr (insubd x).
  proof.
    move=> Px; case (x = RStr.R.zeror) => [->>|neqx0].
    + by rewrite RStr.R.invr0 insubd0 SRStr.R.invr0.
    by rewrite insubdVR // PV.
  qed.

  lemma insubdX x n :
    P x =>
    insubd (RStr.R.exp x n) =
    SRStr.R.exp (insubd x) n.
  proof.
    move=> Px; case (x = RStr.R.zeror) => [->>|neqx0].
    + by rewrite RStr.R.expr0z insubd0 SRStr.R.expr0z fun_if insubd1 insubd0.
    by rewrite insubdXR // PV.
  qed.
end SubField.


(* ==================================================================== *)
theory ZModulePred.
  type t.

  clone import ZModule as R with
    type t <= t.

  op Rpred (P : t -> bool) : bool.

  axiom Rpred0 P : Rpred P => P zeror.

  axiom RpredD P : Rpred P => forall x y , P x => P y => P (x + y).

  axiom RpredN P : Rpred P => forall x , P x => P (-x).
  
  lemma RpredB P : Rpred P => forall x y , P x => P y => P (x - y).
  proof. by move=> RpredP x y Px Py; apply/RpredD/RpredN. qed.

  lemma RpredMz P : Rpred P => forall x n , P x => P (intmul x n).
  proof.
    move=> RpredP x n; wlog: n / 0 <= n => [wlogn|].
    + case (0 <= n) => [|/ltrNge/ltzW/ler_opp2/=] /wlogn // + Px.
      move/(_ Px); rewrite R.mulrNz=> /(RpredN _ RpredP).
      by rewrite opprK.
    elim: n => [|n le0n IHn]; [by rewrite R.mulr0z Rpred0|].
    by rewrite R.mulrSz => Px; move/(_ Px): IHn => P_; apply/RpredD.
  qed.
end ZModulePred.

(* -------------------------------------------------------------------- *)
theory ComRingPred.
  type t.

  clone import ComRing as R with
    type t <= t.

  clone include ZModulePred with
    type t      <- t,
    theory R <- R
    rename [theory] "R" as "Gone".

  axiom Rpred1 P : Rpred P => P oner.
  
  axiom RpredM P : Rpred P => forall x y , P x => P y => P (x * y).

  lemma RpredXR P : Rpred P => forall x n , P x => 0 <= n => P (exp x n).
  proof.
    move=> RpredP x n Px; elim: n => [|n le0n IHn]; [by rewrite R.expr0 Rpred1|].
    by rewrite R.exprS //; apply/RpredM.
  qed.
end ComRingPred.

(* -------------------------------------------------------------------- *)
theory IDomainPred.
  type t.

  clone import IDomain as R with
    type t <= t.

  clone include ComRingPred with
    type t   <- t,
    theory R <- R
    rename [theory] "R" as "Gone".
end IDomainPred.

(* -------------------------------------------------------------------- *)
theory FieldPred.
  type t.

  clone import Field as R with
    type t <= t.

  clone include IDomainPred with
    type t   <- t,
    theory R <- R
    rename [theory] "R" as "Gone".
end FieldPred.


(* ==================================================================== *)
abstract theory SubZModulePred.
  type t, st.

  clone import ZModuleStruct as RStr with
    type t <= t.

  clone import ZModulePred as RPr with
    type t   <= t,
    theory R <= RStr.R.

  clone import Subtype as Sub with
    type T  <= t,
    type sT <= st.

  import Sub.

  axiom RpredP : Rpred P.

  clone import SubZModule as SubR with
    type t           <= t,
    type st          <= st,
    theory RStr      <= RStr,
    theory Sub       <= Sub,
    op SRStr.R.zeror <= insubd RStr.R.zeror,
    op SRStr.R.( + ) <= (fun x y => insubd (RStr.R.( + ) (val x) (val y))),
    op SRStr.R.([-]) <= (fun x => insubd (RStr.R.([-]) (val x)))
  proof *.

  realize SRStr.R.addrA.
  proof.
    move=> x y z; rewrite /( + ); apply/val_inj.
    rewrite !val_insubd (RPr.RpredD _ RpredP (val x) (val y)) ?valP //=.
    rewrite (RPr.RpredD _ RpredP (val y) (val z)) ?valP //=.
    by rewrite RStr.R.addrA.
  qed.

  realize SRStr.R.addrC.
  proof.
    move=> x y; rewrite /( + ); apply/val_inj.
    rewrite !val_insubd !(RPr.RpredD _ RpredP) ?valP //=.
    by rewrite RStr.R.addrC.
  qed.

  realize SRStr.R.add0r.
  proof.
    move=> x; rewrite /zeror /( + ); apply/val_inj.
    by rewrite !val_insubd (RPr.Rpred0 _ RpredP) /= RStr.R.add0r valP.
  qed.

  realize SRStr.R.addNr.
  proof.
    move=> x; rewrite /zeror /( + ) /([-]); apply/val_inj; rewrite !val_insubd.
    by rewrite (RPr.RpredN _ RpredP) ?valP //= RStr.R.addNr (RPr.Rpred0 _ RpredP).
  qed.

  realize val0.
  proof. by rewrite /zeror val_insubd (RPr.Rpred0 _ RpredP). qed.

  realize valD.
  proof.
    move=> x y; rewrite /( + ) val_insubd.
    by rewrite (RPr.RpredD _ RpredP) // valP.
  qed.
end SubZModulePred.

(* -------------------------------------------------------------------- *)
abstract theory SubComRingPred.
  type t, st.

  clone import ComRingStruct as RStr with
    type t <= t.

  clone import ComRingPred as RPr with
    type t   <= t,
    theory R <= RStr.R.

  clone import Subtype as Sub with
    type T  <= t,
    type sT <= st.

  import Sub.

  axiom RpredP : Rpred P.

  clone import SubComRing as SubR with
    type t            <= t,
    type st           <= st,
    theory RStr       <= RStr,
    theory Sub        <= Sub,
    op SRStr.R.zeror  <= insubd RStr.R.zeror,
    op SRStr.R.( + )  <= (fun x y => insubd (RStr.R.( + ) (val x) (val y))),
    op SRStr.R.([-])  <= (fun x => insubd (RStr.R.([-]) (val x))),
    op SRStr.R.oner   <= insubd RStr.R.oner,
    op SRStr.R.( * )  <= (fun x y => insubd (RStr.R.( * ) (val x) (val y))),
    pred SRStr.R.unit <= (fun x => RStr.R.unit (val x)),
    op SRStr.R.invr   <= (fun x => insubd (RStr.R.invr (val x))).

  clone include SubZModulePred with
    type t       <- t ,
    type st      <- st,
    theory RStr  <- RStr,
    theory RPr   <- RPr,
    theory Sub   <- Sub,
    axiom RpredP <- RpredP
    rename [theory] "RStr" as "RStrGone"
           [theory] "RPr"  as "RPrGone"
           [theory] "Sub"  as "SubGone"
    proof RpredP.

  realize zmodulep. by apply/comringpred_zmodule. qed.

  import Sub.

  op oner      = insubd oner.
  op ( * ) x y = insubd (val x * val y).
  op invr x    = insubd (invr (val x)). print unit.
  pred unit x  = unit (val x).

  lemma val1 : val oner = CR.oner.
  proof. by rewrite /oner val_insubd comring1. qed.

  lemma valM x y : val (x * y) = val x * val y.
  proof. by rewrite /( * ) val_insubd comringM // valP. qed.

  lemma valV x : val (invr x) = invr (val x).
  proof. by rewrite /invr val_insubd comringV // valP. qed.

  lemma insubd1 : insubd CR.oner = oner.
  proof. by rewrite /oner. qed.

  lemma insubdM x y : p x => p y => insubd (x * y) = insubd x * insubd y.
  proof.
    move=> px py; rewrite /insubd; move: (insubT _ px) (insubT _ py).
    by case: (insub x) => // ox /= <<-; case: (insub y) => // oy /= <<-.
  qed.

  lemma insubdV x : p x => insubd (invr x) = invr (insubd x).
  proof.
    move=> px; rewrite /insubd; move: (insubT _ px).
    by case: (insub x) => // ox /= <<-.
  qed.

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
  proof. by move=> x y z; apply/val_inj; rewrite !valM mulrA. qed.

  realize mulrC.
  proof. by move=> x y; apply/val_inj; rewrite !valM mulrC. qed.

  realize mul1r.
  proof. by move=> x; apply/val_inj; rewrite valM val1 mul1r. qed.

  realize mulrDl.
  proof. by move=> x y z; apply/val_inj; rewrite valD !valM valD mulrDl. qed.

  realize mulVr.
  proof. by move=> x ?; apply/val_inj; rewrite valM valV val1 mulVr. qed.

  realize unitP.
  proof. by move=> x y /(congr1 val); rewrite valM val1 => /unitP. qed.

  realize unitout.
  proof. by move=> x ?; apply/val_inj; rewrite valV unitout. qed.

  lemma insubdX x n : p x => insubd (exp x n) = exp (insubd x) n.
  proof.
    wlog: n / 0 <= n => [wlogn|].
    + case (0 <= n) => [|/ltrNge/ltzW/ler_opp2/=] /wlogn // + px.
      by move/(_ px); rewrite CR.exprN SCR.exprN insubdV ?comringX // => /SCR.invr_inj.
    elim: n => [|n le0n IHn]; [by rewrite CR.expr0 SCR.expr0|].
    by rewrite CR.exprS // SCR.exprS // => px; rewrite -IHn // insubdM // comringX.
  qed.

  lemma valX (x : st) n : val (exp x n) = exp (val x) n.
  proof.
    rewrite -valKd -insubdX ?valP //.
    by rewrite valKd val_insubd comringX // valP.
  qed.
end SubComRing.

(* -------------------------------------------------------------------- *)
abstract theory SubIDomain.
  type t, st.

  clone import IDomain as ID with
    type t <= t.

  clone import IDomainPred as IDPr with
    type t    <= t,
    theory ID <= ID.

  op p : t -> bool.

  axiom idomainp : idomainpred p.

  hint exact : idomainp.

  clone include SubComRing with
    type t  <- t ,
    type st <- st,
    op    p <- p ,
    theory ZMod <= ID,
    theory CR   <= ID,
    theory ZModPr <= IDPr,
    theory CRPr <= IDPr
    proof comringp.

  realize comringp. by apply/idomainpred_comring. qed.

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
    move => x y; split => [eq_|[->>|->>]]; last 2 by apply/val_inj; rewrite valM val0 mulf_eq0.
    by move: (mulf_eq0 (val x) (val y)); rewrite -valM eq_ val0 /= -val0; case => ?; [left|right]; apply/val_inj.
  qed.
end SubIDomain.

(* -------------------------------------------------------------------- *)
abstract theory SubField.
  type t, st.

  clone import Field as F with
    type t <= t.

  clone import FieldPred as FPr with
    type t   <= t,
    theory F <= F.

  op p : t -> bool.

  axiom fieldp : fieldpred p.

  hint exact : fieldp.

  clone include SubIDomain with
    type t  <- t ,
    type st <- st,
    op    p <- p ,
    theory ZMod   <= F,
    theory CR   <= F,
    theory ID   <= F,
    theory ZModPr <= FPr,
    theory CRPr <= FPr,
    theory IDPr <= FPr
    proof idomainp.

  realize idomainp. by apply/fieldpred_idomain. qed.

  import Sub.

  clone import Field as SF with
    type t    <= st,
    op zeror  <= zeror,
    op (+)    <= (+),
    op [-]    <= ([-]),
    op oner   <= oner,
    op ( * )  <= ( * ),
    op invr   <= invr,
    pred unit <= unit
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
  realize mulVr     by exact SID.mulVr.
  realize unitP     by exact SID.unitP.
  realize unitout   by exact SID.unitout.
  realize mulf_eq0  by exact SID.mulf_eq0.

  realize unitfP.
  proof.
    move => x; apply/contraLR => /= neg_unit; apply/val_inj; rewrite val0.
    by move: neg_unit; apply/contraLR => /= /unitfP.
  qed.
end SubField.


(* ==================================================================== *)
abstract theory UZMod_ComRing.
  type t, uz.

  clone import ComRing as CR with
    type t <= t.

  clone import Subtype as Sub with
    type T  <= t,
    type sT <= uz,
    pred P  <= CR.unit.

  op oner = insubd oner.
  op ( * ) x y = insubd (val x * val y).
  op invr x = insubd (invr (val x)).

  lemma val1 : val oner = CR.oner.
  proof. by rewrite /oner val_insubd unitr1. qed.

  lemma valM x y : val (x * y) = val x * val y.
  proof. by rewrite /( * ) val_insubd unitrM !valP. qed.

  lemma valV x : val (invr x) = invr (val x).
  proof. by rewrite /invr val_insubd unitrV valP. qed.

  clone import ZModule as UZMod with
    type t    <= uz,
    op zeror  <= oner,
    op (+)    <= ( * ),
    op [-]    <= invr
    proof *.

  realize addrA.
  proof. by move => x y z; apply/val_inj; rewrite !valM mulrA. qed.

  realize addrC.
  proof. by move => x y; apply/val_inj; rewrite !valM mulrC. qed.

  realize add0r.
  proof. by move => x; apply/val_inj; rewrite valM val1 mul1r. qed.

  realize addNr.
  proof. by move => x; apply/val_inj; rewrite valM valV val1 mulVr // valP. qed.

  clone import ZModuleStruct as UZModStr with
    type t      <= uz,
    theory ZMod <= UZMod.

  lemma val_intmul_ge0 x n :
    0 <= n =>
    val (UZMod.intmul x n) = exp (val x) n.
  proof.
    elim n => [|n le0n IHn]; [by rewrite mulr0z expr0 val1|].
    by rewrite mulrSz valM IHn exprS.
  qed.
end UZMod_ComRing.

(* -------------------------------------------------------------------- *)
abstract theory UZMod_IDomain.
  type t, uz.

  clone import IDomain as ID with
    type t <= t.

  clone include UZMod_ComRing with
    type t    <- t,
    type uz   <- uz,
    theory CR <= ID.
end UZMod_IDomain.

(* -------------------------------------------------------------------- *)
abstract theory UZMod_Field.
  type t, uz.

  clone import Field as F with
    type t <= t.

  clone include UZMod_IDomain with
    type t    <- t,
    type uz   <- uz,
    theory CR <= F,
    theory ID <= F.

  lemma val_intmul x n :
    Sub.val (UZMod.intmul x n) = exp (Sub.val x) n.
  proof.
    case (0 <= n) => [|/ltrNge/ltzW]; [by apply/val_intmul_ge0|].
    rewrite -(IntID.opprK n) oppr_le0 => le0_.
    by rewrite UZMod.mulrNz valV exprN; congr; apply/val_intmul_ge0.
  qed.
end UZMod_Field.







