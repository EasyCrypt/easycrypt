(* -------------------------------------------------------------------- *)
require import AllCore List Ring Int IntDiv Bigalg RingStruct FinType.
(*---*) import StdOrder.IntOrder.

(* ==================================================================== *)
theory ZModuleMorph.
  type t1, t2.

  clone include ZModuleStruct with
    type t <- t1
    rename [theory] "RL"  as "RL1"
    rename [theory] "Str" as "Str1".

  clone include ZModuleStruct with
    type t <- t2
    rename [theory] "RL"  as "RL2"
    rename [theory] "Str" as "Str2".

  theory ZModMorph.
    import RL1 RL2 ZModStr1 ZModStr2.

    pred zmod_homo f =
      morphism_0 f RL1.zeror RL2.zeror /\
      morphism_2 f RL1.(+) RL2.(+).

    lemma zmod_endo_homo_comp f g :
      ZModStr1.zmod_endo f =>
      zmod_homo g =>
      zmod_homo (g \o f).
    proof.
      rewrite /ZModStr1.zmod_endo /zmod_homo /(\o) => |> f0 fD g0 gD /=; split.
      + by rewrite /morphism_0 f0 g0.
      by move=> ? ?; rewrite fD gD.
    qed.

    lemma zmod_homo_endo_comp f g :
      zmod_homo f =>
      ZModStr2.zmod_endo g =>
      zmod_homo (g \o f).
    proof.
      rewrite /zmod_homo /ZModStr2.zmod_endo /(\o) => |> f0 fD g0 gD /=; split.
      + by rewrite /morphism_0 f0 g0.
      by move=> ? ?; rewrite fD gD.
    qed.

    lemma zmod_homo0 f :
      zmod_homo f =>
      morphism_0 f RL1.zeror RL2.zeror.
    proof. by case. qed.

    lemma zmod_homoD f :
      zmod_homo f =>
      morphism_2 f RL1.(+) RL2.(+).
    proof. by case. qed.

    lemma zmod_homoN f :
      zmod_homo f =>
      morphism_1 f RL1.([-]) RL2.([-]).
    proof. by move=> ef x; rewrite -RL2.addr_eq0 -zmod_homoD // RL1.addNr zmod_homo0. qed.

    lemma zmod_homoB f :
      zmod_homo f =>
      morphism_2 f RL1.( - ) RL2.( - ).
    proof. by move=> ef x y; rewrite zmod_homoD // zmod_homoN. qed.

    lemma zmod_homoMz f :
      zmod_homo f =>
      forall x n , f (RL1.intmul x n) = RL2.intmul (f x) n.
    proof.
      move => ef x n; wlog: x n / 0 <= n => [wlog|].
      + case (0 <= n) => [|/ltrNge/ltzW/oppr_ge0]; [by apply/wlog|].
        by move => /wlog /(_ (RL1.([-]) x)); rewrite zmod_homoN // RL1.mulNrNz RL2.mulNrNz.
      elim: n => [|n le0n IHn]; [by rewrite RL1.mulr0z RL2.mulr0z zmod_homo0|].
      by rewrite RL1.mulrS // RL2.mulrS // zmod_homoD // IHn.
    qed.

    lemma zmod_homo_order f :
      zmod_homo f =>
      forall x , order (f x) %| order x.
    proof. by move=> ef x; rewrite dvd_order -zmod_homoMz // intmul_order zmod_homo0. qed.

    lemma zmod_homo_orbit f :
      zmod_homo f =>
      forall x y ,
        ZModStr1.orbit x y => ZModStr2.orbit (f x) (f y).
    proof.
      move=> ef x y [n] ->>; rewrite zmod_homoMz //.
      by apply/orbitMz/orbit_refl.
    qed.
  
    lemma zmod_homo_orbit_list f :
      zmod_homo f =>
      forall x ,
        0 < order (f x) =>
        flatten (nseq (order x %/ order (f x)) (orbit_list (f x))) = map f (orbit_list x).
    proof.
      move=> ef x lt0__; case/ler_eqVlt: (ZModStr1.ge0_order x) => [/eq_sym eq_|lt0_].
      + by move/ZModStr1.orbit_list_nil: (eq_) => ->; rewrite eq_ /= nseq0 flatten_nil.
      case/dvdzP: (zmod_homo_order _ ef x) => q eq_; move: (lt0_); rewrite eq_.
      rewrite pmulr_lgt0 // => lt0q; rewrite mulzK; [by apply/gtr_eqF|].
      rewrite /orbit_list eq_; move/ltzW: lt0q => {eq_}.
      elim: q => [|n le0n IHn]; [rewrite /= !mkseq0 /=|].
      + by rewrite nseq0 flatten_nil.
      rewrite nseqSr // -cats1 flatten_cat flatten_seq1.
      rewrite mulrDl /= mkseq_add; [|by apply/ge0_order|].
      + by apply/mulr_ge0 => //; apply/ge0_order.
      rewrite map_cat IHn; congr; [by apply/eq_in_map|].
      rewrite map_mkseq; apply/eq_in_mkseq => i /mem_range memi.
      by rewrite /(\o) /= zmod_homoMz // mulrDz mulrC mulrM intmul_order mul0i add0r.
    qed.
  
    lemma zmod_homo_eqv_orbit f :
      zmod_homo f =>
      forall x y z ,
        ZModStr1.eqv_orbit x y z =>
        eqv_orbit (f x) (f y) (f z).
    proof. by move=> ef x y z; rewrite /eqv_orbit -zmod_homoB //; apply/zmod_homo_orbit. qed.

    lemma subzmod_subzmod_zmod_homo f P :
      zmod_homo f =>
      ZModStr2.subzmod P =>
      subzmod (P \o f).
    proof.
      move=> ef sP; rewrite /(\o); split; [|split].
      + by rewrite zmod_homo0 // subzmod0.
      + by move=> x y; rewrite zmod_homoD //; apply/subzmodD.
      by move=> x; rewrite zmod_homoN //; apply/subzmodN.
    qed.

    lemma subzmod_zmod_homo_subzmod f P :
      zmod_homo f =>
      ZModStr1.subzmod P =>
      subzmod (fun y => exists x , f x = y /\ P x).
    proof.
      move=> ef sP; split; [|split].
      + by exists RL1.zeror; rewrite zmod_homo0 // subzmod0.
      + move=> ? ? [x] [] <<- Px [y] [] <<- Py; exists (x + y).
        by rewrite zmod_homoD // subzmodD.
      move=> ? [x] [] <<- Px; exists (-x).
      by rewrite zmod_homoN // subzmodN.
    qed.

    pred zmod_mono f =
      injective f /\
      zmod_homo f.

    lemma zmod_mono_inj f :
      zmod_mono f => injective f.
    proof. by case. qed.

    lemma zmod_mono_homo f :
      zmod_mono f => zmod_homo f.
    proof. by case. qed.

    lemma zmod_mono_endo_mono_comp f g :
      ZModStr1.zmod_mono_endo f =>
      zmod_mono g =>
      zmod_mono (g \o f).
    proof.
      by case=> injf ef [] injg eg; split; [apply/inj_comp|apply/zmod_endo_homo_comp].
    qed.

    lemma zmod_mono_mono_endo_comp f g :
      zmod_mono f =>
      ZModStr2.zmod_mono_endo g =>
      zmod_mono (g \o f).
    proof.
      by case=> injf ef [] injg eg; split; [apply/inj_comp|apply/zmod_homo_endo_comp].
    qed.

    lemma zmod_mono0 f :
      zmod_mono f =>
      morphism_0 f RL1.zeror RL2.zeror.
    proof. by move/zmod_mono_homo/zmod_homo0. qed.

    lemma zmod_monoD f :
      zmod_mono f =>
      morphism_2 f RL1.(+) RL2.(+).
    proof. by move/zmod_mono_homo/zmod_homoD. qed.

    lemma zmod_monoN f :
      zmod_mono f =>
      morphism_1 f RL1.([-]) RL2.([-]).
    proof. by move/zmod_mono_homo/zmod_homoN. qed.

    lemma zmod_monoB f :
      zmod_mono f =>
      morphism_2 f RL1.( - ) RL2.( - ).
    proof. by move/zmod_mono_homo/zmod_homoB. qed.

    lemma zmod_monoMz f :
      zmod_mono f =>
      forall x n , f (RL1.intmul x n) = intmul (f x) n.
    proof. by move/zmod_mono_homo/zmod_homoMz. qed.

    lemma zmod_mono_eq0 f :
      zmod_mono f =>
      forall x , f x = RL2.zeror <=> x = RL1.zeror.
    proof.
      move=> ief x; split=> [|->>]; [|by apply/zmod_mono0].
      by move/zmod_mono_inj/(_ x RL1.zeror): (ief); rewrite zmod_mono0.
    qed.

    lemma zmod_monoP0 f :
      zmod_mono f <=>
      ( (forall x , f x = RL2.zeror => x = RL1.zeror) /\
        zmod_homo f ).
    proof.
      split=> [ief|[eq0 ef]]; [by split=> [x|]; [rewrite zmod_mono_eq0|apply/zmod_mono_homo]|].
      by split=> // x y; rewrite -subr_eq0 -zmod_homoB // => /eq0 /RL1.subr_eq0.
    qed.

    lemma zmod_mono_order f :
      zmod_mono f =>
      forall x , order (f x) = order x.
    proof.
      move=> ef x; move: (dvdz_anti (order (f x)) (order x) _ _).
      + by apply/zmod_homo_order/zmod_mono_homo.
      + rewrite dvd_order -(zmod_mono_eq0 _ ef) zmod_monoMz //.
        by rewrite intmul_order.
      by rewrite !ger0_norm // ge0_order.
    qed.

    lemma zmod_mono_orbit f :
      zmod_mono f =>
      forall x y ,
        orbit (f x) (f y) = orbit x y.
    proof.
      move=> ef x y; apply/eq_iff; split; [|by apply/zmod_homo_orbit/zmod_mono_homo].
      case=> n; rewrite -zmod_monoMz // => /(zmod_mono_inj _ ef) ->>.
      by apply/ZModStr1.orbitMz/ZModStr1.orbit_refl.
    qed.
  
    lemma zmod_mono_orbit_list f :
      zmod_mono f =>
      forall x ,
        orbit_list (f x) = map f (orbit_list x).
    proof.
      move=> ef x; case/ler_eqVlt: (ZModStr1.ge0_order x) => [/eq_sym eq_|lt0_].
      + move/ZModStr1.orbit_list_nil: (eq_) => ->; move: eq_; rewrite -(zmod_mono_order _ ef).
        by move/orbit_list_nil => ->.
      rewrite -zmod_homo_orbit_list ?zmod_mono_homo ?zmod_mono_order //.
      by rewrite divzz gtr_eqF //= b2i1 nseq1 flatten_seq1.
    qed.
  
    lemma zmod_mono_eqv_orbit f :
      zmod_mono f =>
      forall x y z ,
        eqv_orbit (f x) (f y) (f z) =
        eqv_orbit x y z.
    proof. by move=> ef x y z; rewrite /eqv_orbit -zmod_monoB // zmod_mono_orbit. qed.

    lemma subzmod_subzmod_zmod_mono f P :
      zmod_mono f =>
      ZModStr2.subzmod P =>
      subzmod (P \o f).
    proof. by move/zmod_mono_homo/subzmod_subzmod_zmod_homo/(_ P). qed.

    lemma subzmod_zmod_mono_subzmod f P :
      zmod_mono f =>
      ZModStr1.subzmod P =>
      subzmod (fun y => exists x , f x = y /\ P x).
    proof. by move/zmod_mono_homo/subzmod_zmod_homo_subzmod/(_ P). qed.

    pred zmod_iso f =
      surjective f /\
      zmod_mono f.

    lemma zmod_iso_inj f :
      zmod_iso f => injective f.
    proof. by case=> _ /zmod_mono_inj. qed.

    lemma zmod_iso_surj f :
      zmod_iso f => surjective f.
    proof. by case. qed.

    lemma zmod_iso_bij f :
      zmod_iso f => bijective f.
    proof. by move=> af; apply/bij_inj_surj; rewrite zmod_iso_inj // zmod_iso_surj. qed.

    lemma zmod_iso_mono f :
      zmod_iso f => zmod_mono f.
    proof. by case. qed.

    lemma zmod_iso_endo f :
      zmod_iso f => zmod_homo f.
    proof. by move/zmod_iso_mono/zmod_mono_homo. qed.

    lemma zmod_isoP f :
      zmod_iso f <=> (bijective f /\ zmod_homo f).
    proof.
      split=> [af|[/bij_inj_surj [injf surjf] ef]]; split=> //.
      + by apply/zmod_iso_bij.
      by apply/zmod_iso_endo.
    qed.

    lemma zmod_auto_iso_comp f g :
      ZModStr1.zmod_auto f =>
      zmod_iso g =>
      zmod_iso (g \o f).
    proof.
      case/ZModStr1.zmod_autoP=> bijf ef /zmod_isoP [] bijg eg; apply/zmod_isoP.
      by split; [apply/bij_comp|apply/zmod_endo_homo_comp].
    qed.

    lemma zmod_iso_auto_comp f g :
      zmod_iso f =>
      ZModStr2.zmod_auto g =>
      zmod_iso (g \o f).
    proof.
      case/zmod_isoP=> bijf ef /ZModStr2.zmod_autoP [] bijg eg; apply/zmod_isoP.
      by split; [apply/bij_comp|apply/zmod_homo_endo_comp].
    qed.

    lemma zmod_iso0 f :
      zmod_iso f =>
      morphism_0 f RL1.zeror RL2.zeror.
    proof. by move/zmod_iso_mono/zmod_mono0. qed.

    lemma zmod_isoD f :
      zmod_iso f =>
      morphism_2 f RL1.(+) RL2.(+).
    proof. by move/zmod_iso_mono/zmod_monoD. qed.

    lemma zmod_isoN f :
      zmod_iso f =>
      morphism_1 f RL1.([-]) RL2.([-]).
    proof. by move/zmod_iso_mono/zmod_monoN. qed.

    lemma zmod_isoB f :
      zmod_iso f =>
      morphism_2 f RL1.( - ) RL2.( - ).
    proof. by move/zmod_iso_mono/zmod_monoB. qed.

    lemma zmod_isoMz f :
      zmod_iso f =>
      forall x n , f (RL1.intmul x n) = RL2.intmul (f x) n.
    proof. by move/zmod_iso_mono/zmod_monoMz. qed.

    lemma zmod_iso_eq0 f :
      zmod_iso f =>
      forall x , f x = RL2.zeror <=> x = RL1.zeror.
    proof. by move/zmod_iso_mono/zmod_mono_eq0. qed.

    lemma zmod_iso_order f :
      zmod_iso f =>
      forall x , order (f x) = order x.
    proof. by move/zmod_iso_mono/zmod_mono_order. qed.

    lemma zmod_iso_orbit f :
      zmod_iso f =>
      forall x y ,
        orbit (f x) (f y) = orbit x y.
    proof. by move/zmod_iso_mono/zmod_mono_orbit. qed.
  
    lemma zmod_iso_orbit_list f :
      zmod_iso f =>
      forall x ,
        orbit_list (f x) = map f (orbit_list x).
    proof. by move/zmod_iso_mono/zmod_mono_orbit_list. qed.
  
    lemma zmod_iso_eqv_orbit f :
      zmod_iso f =>
      forall x y z ,
        eqv_orbit (f x) (f y) (f z) =
        eqv_orbit x y z.
    proof. by move/zmod_iso_mono/zmod_mono_eqv_orbit. qed.

    lemma subzmod_subzmod_zmod_iso f P :
      zmod_iso f =>
      ZModStr2.subzmod P =>
      subzmod (P \o f).
    proof. by move/zmod_iso_mono/subzmod_subzmod_zmod_mono/(_ P). qed.

    lemma subzmod_zmod_iso_subzmod f P :
      zmod_iso f =>
      ZModStr1.subzmod P =>
      subzmod (fun y => exists x , f x = y /\ P x).
    proof. by move/zmod_iso_mono/subzmod_zmod_mono_subzmod/(_ P). qed.
  end ZModMorph.
end ZModuleMorph.

(* -------------------------------------------------------------------- *)
theory ComRingMorph.
  type t1, t2.

  clone include ComRingStruct with
    type t <- t1
    rename [theory] "RL"  as "RL1"
    rename [theory] "Str" as "Str1".

  clone include ComRingStruct with
    type t <- t2
    rename [theory] "RL"  as "RL2"
    rename [theory] "Str" as "Str2".

  clone include ZModuleMorph with
    type t1 <- t1,
    type t2 <- t2,
    theory RL1 <- RL1,
    theory RL2 <- RL2,
    theory ZModStr1 <- ZModStr1,
    theory ZModStr2 <- ZModStr2
    rename [theory] "RL"  as "Gone"
           [theory] "Str" as "Gone".

  theory CRMorph.
    import RL1 RL2 ZModStr1 ZModStr2 CRStr1 CRStr2 ZModMorph.

    pred cr_homo f =
      zmod_homo f /\
      morphism_0 f RL1.oner RL2.oner /\
      morphism_2 f RL1.( * ) RL2.( * ).

    lemma cr_homo_zmod f :
      cr_homo f => zmod_homo f.
    proof. by case. qed.

    lemma cr_endo_homo_comp f g :
      CRStr1.cr_endo f =>
      cr_homo g =>
      cr_homo (g \o f).
    proof.
      case=> ef [] f1 fM [] eg [] g1 gM; split; [by apply/zmod_endo_homo_comp|split].
      + by rewrite /(\o) /morphism_0 f1 g1.
      by move=> x y; rewrite /(\o) fM gM.
    qed.

    lemma cr_homo_endo_comp f g :
      cr_homo f =>
      CRStr2.cr_endo g =>
      cr_homo (g \o f).
    proof.
      case=> ef [] f1 fM [] eg [] g1 gM; split; [by apply/zmod_homo_endo_comp|split].
      + by rewrite /(\o) /morphism_0 f1 g1.
      by move=> x y; rewrite /(\o) fM gM.
    qed.

    lemma cr_homo0 f :
      cr_homo f =>
      morphism_0 f RL1.zeror RL2.zeror.
    proof. by move/cr_homo_zmod/zmod_homo0. qed.

    lemma cr_homoD f :
      cr_homo f =>
      morphism_2 f RL1.(+) RL2.(+).
    proof. by move/cr_homo_zmod/zmod_homoD. qed.

    lemma cr_homoN f :
      cr_homo f =>
      morphism_1 f RL1.([-]) RL2.([-]).
    proof. by move/cr_homo_zmod/zmod_homoN. qed.

    lemma cr_homoB f :
      cr_homo f =>
      morphism_2 f RL1.( - ) RL2.( - ).
    proof. by move/cr_homo_zmod/zmod_homoB. qed.

    lemma cr_homoMz f :
      cr_homo f =>
      forall x n , f (RL1.intmul x n) = RL2.intmul (f x) n.
    proof. by move/cr_homo_zmod/zmod_homoMz. qed.

    lemma cr_homo1 f :
      cr_homo f =>
      morphism_0 f RL1.oner RL2.oner.
    proof. by case => _ []. qed.
  
    lemma cr_homoM f :
      cr_homo f =>
      morphism_2 f RL1.( * ) RL2.( * ).
    proof. by case => _ []. qed.
  
    lemma cr_homoUR f :
      cr_homo f =>
      forall x ,
        RL1.unit x =>
        RL2.unit (f x).
    proof.
      move=> ef x /RL1.unitrP [y] eq_; apply/unitrP; exists (f y).
      by rewrite -cr_homoM // eq_ cr_homo1.
    qed.
  
    lemma cr_homoVR f :
      cr_homo f =>
      forall x ,
        f (RL1.invr x) =
        if RL1.unit x
        then RL2.invr (f x)
        else f x.
    proof.
      move=> ef x; case (unit x) => [ux|Nux].
      + apply/(mulIr (f x)); [by apply/cr_homoUR|].
        by rewrite -cr_homoM // !mulVr ?cr_homo1 // cr_homoUR.
      by rewrite unitout.
    qed.
  
    lemma cr_homoZ f :
      cr_homo f =>
      forall n , f (RL1.ofint n) = RL2.ofint n.
    proof. by move=> ef n; rewrite /ofint cr_homoMz // cr_homo1. qed.
  
    lemma cr_homoXR f :
      cr_homo f =>
      forall x n ,
        f (RL1.exp x n) =
        if unit x
        then RL2.exp (f x) n
        else RL2.exp (f x) `|n|.
    proof.
      move=> ef x n; wlog: n x / 0 <= n => [wlogn|].
      + case (0 <= n) => [/wlogn -> //|/ltrNge/ltzW].
        move=> len0; move/ler_opp2: (len0) => /= /wlogn {wlogn} /(_ (invr x)).
        rewrite (ler0_norm n) // ger0_norm; [by apply/ler_opp2|].
        rewrite -!exprV invrK unitrV (cr_homoVR _ ef) => ->.
        by case: (unit x) => //; rewrite invrK.
      move=> le0n; rewrite ger0_norm //; elim: n le0n => [|n le0n IHn].
      + by rewrite !expr0 cr_homo1.
      by rewrite !exprS // cr_homoM // IHn; case (unit x).
    qed.

    lemma cr_homo_order f :
      cr_homo f =>
      forall x , order (f x) %| order x.
    proof. by move/cr_homo_zmod/zmod_homo_order. qed.

    lemma cr_homo_orbit f :
      cr_homo f =>
      forall x y ,
        ZModStr1.orbit x y => ZModStr2.orbit (f x) (f y).
    proof. by move/cr_homo_zmod/zmod_homo_orbit. qed.
  
    lemma cr_homo_orbit_list f :
      cr_homo f =>
      forall x ,
        0 < order (f x) =>
        flatten (nseq (order x %/ order (f x)) (orbit_list (f x))) = map f (orbit_list x).
    proof. by move/cr_homo_zmod/zmod_homo_orbit_list. qed.
  
    lemma cr_homo_eqv_orbit f :
      cr_homo f =>
      forall x y z ,
        ZModStr1.eqv_orbit x y z =>
        ZModStr2.eqv_orbit (f x) (f y) (f z).
    proof. by move/cr_homo_zmod/zmod_homo_eqv_orbit. qed.

    lemma subcr_subcr_cr_homo f P :
      cr_homo f =>
      CRStr2.subcr P =>
      subcr (P \o f).
    proof.
      move=> ef sP; rewrite /(\o); split; [|split].
      + by apply/subzmod_subzmod_zmod_homo; [apply/cr_homo_zmod|apply/subcr_zmod].
      + by rewrite cr_homo1 // subcr1.
      by move=> x y; rewrite cr_homoM //; apply/subcrM.
    qed.

    lemma subcr_cr_homo_subcr f P :
      cr_homo f =>
      CRStr1.subcr P =>
      subcr (fun y => exists x , f x = y /\ P x).
    proof.
      move=> ef sP; rewrite /(\o); split; [|split].
      + by apply/subzmod_zmod_homo_subzmod; [apply/cr_homo_zmod|apply/CRStr1.subcr_zmod].
      + by exists RL1.oner; rewrite cr_homo1 // subcr1.
      move=> ? ? [x] [] <<- Px [y] [] <<- Py; exists (x * y).
      by rewrite cr_homoM // subcrM.
    qed.

    lemma cr_homo_char f :
      cr_homo f =>
      CRStr2.char %| CRStr1.char.
    proof. by move=> ef; rewrite /char -(cr_homo1 _ ef) cr_homo_order. qed.

    pred cr_mono f =
      injective f /\
      cr_homo f.

    lemma cr_mono_inj f :
      cr_mono f => injective f.
    proof. by case. qed.

    lemma cr_mono_homo f :
      cr_mono f => cr_homo f.
    proof. by case. qed.

    lemma cr_mono_zmod f :
      cr_mono f => zmod_mono f.
    proof.
      by move=> ef; split; [apply/cr_mono_inj|apply/cr_homo_zmod/cr_mono_homo].
    qed.

    lemma cr_mono_zmod_homo f :
      cr_mono f => zmod_homo f.
    proof. by move/cr_mono_homo/cr_homo_zmod. qed.

    lemma cr_mono_endo_mono_comp f g :
      CRStr1.cr_mono_endo f =>
      cr_mono g =>
      cr_mono (g \o f).
    proof.
      by case=> injf ef [] injg eg; split; [apply/inj_comp|apply/cr_endo_homo_comp].
    qed.

    lemma cr_mono_mono_endo_comp f g :
      cr_mono f =>
      CRStr2.cr_mono_endo g =>
      cr_mono (g \o f).
    proof.
      by case=> injf ef [] injg eg; split; [apply/inj_comp|apply/cr_homo_endo_comp].
    qed.

    lemma cr_mono0 f :
      cr_mono f =>
      morphism_0 f RL1.zeror RL2.zeror.
    proof. by move/cr_mono_homo/cr_homo0. qed.

    lemma cr_monoD f :
      cr_mono f =>
      morphism_2 f RL1.(+) RL2.(+).
    proof. by move/cr_mono_homo/cr_homoD. qed.

    lemma cr_monoN f :
      cr_mono f =>
      morphism_1 f RL1.([-]) RL2.([-]).
    proof. by move/cr_mono_homo/cr_homoN. qed.

    lemma cr_monoB f :
      cr_mono f =>
      morphism_2 f RL1.( - ) RL2.( - ).
    proof. by move/cr_mono_homo/cr_homoB. qed.

    lemma cr_monoMz f :
      cr_mono f =>
      forall x n , f (RL1.intmul x n) = RL2.intmul (f x) n.
    proof. by move/cr_mono_homo/cr_homoMz. qed.

    lemma cr_mono1 f :
      cr_mono f =>
      morphism_0 f RL1.oner RL2.oner.
    proof. by move/cr_mono_homo/cr_homo1. qed.
  
    lemma cr_monoM f :
      cr_mono f =>
      morphism_2 f RL1.( * ) RL2.( * ).
    proof. by move/cr_mono_homo/cr_homoM. qed.
  
    lemma cr_monoUR f :
      cr_mono f =>
      forall x ,
        RL1.unit x =>
        RL2.unit (f x).
    proof. by move/cr_mono_homo/cr_homoUR. qed.
  
    lemma cr_monoVR f :
      cr_mono f =>
      forall x ,
        f (RL1.invr x) =
        if RL1.unit x
        then RL2.invr (f x)
        else f x.
    proof. by move/cr_mono_homo/cr_homoVR. qed.
  
    lemma cr_monoZ f :
      cr_mono f =>
      forall n , f (RL1.ofint n) = RL2.ofint n.
    proof. by move/cr_mono_homo/cr_homoZ. qed.
  
    lemma cr_monoXR f :
      cr_mono f =>
      forall x n ,
        f (RL1.exp x n) =
        if unit x
        then RL2.exp (f x) n
        else RL2.exp (f x) `|n|.
    proof. by move/cr_mono_homo/cr_homoXR. qed.

    lemma cr_mono_eq0 f :
      cr_mono f =>
      forall x , f x = RL2.zeror <=> x = RL1.zeror.
    proof. by move/cr_mono_zmod/zmod_mono_eq0. qed.

    lemma cr_monoP0 f :
      cr_mono f <=>
      ( (forall x , f x = RL2.zeror => x = RL1.zeror) /\
        cr_homo f ).
    proof. by rewrite /cr_homo 2!andbA -zmod_monoP0 /cr_mono /cr_homo -!andbA. qed.

    lemma cr_mono_order f :
      cr_mono f =>
      forall x , ZModStr2.order (f x) = ZModStr1.order x.
    proof. by move/cr_mono_zmod/zmod_mono_order. qed.

    lemma cr_mono_orbit f :
      cr_mono f =>
      forall x y ,
        orbit (f x) (f y) = orbit x y.
    proof. by move/cr_mono_zmod/zmod_mono_orbit. qed.
  
    lemma cr_mono_orbit_list f :
      cr_mono f =>
      forall x ,
        orbit_list (f x) = map f (orbit_list x).
    proof. by move/cr_mono_zmod/zmod_mono_orbit_list. qed.
  
    lemma cr_mono_eqv_orbit f :
      cr_mono f =>
      forall x y z ,
        eqv_orbit (f x) (f y) (f z) =
        eqv_orbit x y z.
    proof. by move/cr_mono_zmod/zmod_mono_eqv_orbit. qed.

    lemma subcr_subcr_cr_mono f P :
      cr_mono f =>
      CRStr2.subcr P =>
      subcr (P \o f).
    proof. by move/cr_mono_homo/subcr_subcr_cr_homo/(_ P). qed.

    lemma subcr_cr_mono_subcr f P :
      cr_mono f =>
      CRStr1.subcr P =>
      subcr (fun y => exists x , f x = y /\ P x).
    proof. by move/cr_mono_homo/subcr_cr_homo_subcr/(_ P). qed.

    lemma cr_mono_char f :
      cr_mono f =>
      CRStr1.char = CRStr2.char.
    proof. by move=> ef; rewrite /char -(cr_mono1 _ ef) cr_mono_order. qed.

    pred cr_iso f =
      surjective f /\
      cr_mono f.

    lemma cr_iso_inj f :
      cr_iso f => injective f.
    proof. by case=> _ /cr_mono_inj. qed.

    lemma cr_iso_surj f :
      cr_iso f => surjective f.
    proof. by case. qed.

    lemma cr_iso_bij f :
      cr_iso f => bijective f.
    proof. by move=> af; apply/bij_inj_surj; rewrite cr_iso_inj // cr_iso_surj. qed.

    lemma cr_iso_mono f :
      cr_iso f => cr_mono f.
    proof. by case. qed.

    lemma cr_iso_homo f :
      cr_iso f => cr_homo f.
    proof. by move/cr_iso_mono/cr_mono_homo. qed.

    lemma cr_iso_zmod f :
      cr_iso f => zmod_iso f.
    proof.
      move=> ef; split.
      + by apply/cr_iso_surj.
      by apply/cr_mono_zmod/cr_iso_mono.
    qed.

    lemma cr_iso_zmod_mono f :
      cr_iso f => zmod_mono f.
    proof. by move/cr_iso_zmod/zmod_iso_mono. qed.

    lemma cr_iso_zmod_homo f :
      cr_iso f => zmod_homo f.
    proof. by move/cr_iso_zmod/zmod_iso_endo. qed.

    lemma cr_isoP f :
      cr_iso f <=> (bijective f /\ cr_homo f).
    proof.
      split=> [af|[/bij_inj_surj [injf surjf] ef]]; split=> //.
      + by apply/cr_iso_bij.
      by apply/cr_iso_homo.
    qed.

    lemma cr_auto_iso_comp f g :
      CRStr1.cr_auto f =>
      cr_iso g =>
      cr_iso (g \o f).
    proof.
      case/CRStr1.cr_autoP=> bijf ef /cr_isoP [] bijg eg; apply/cr_isoP.
      by split; [apply/bij_comp|apply/cr_endo_homo_comp].
    qed.

    lemma cr_iso_auto_comp f g :
      cr_iso f =>
      CRStr2.cr_auto g =>
      cr_iso (g \o f).
    proof.
      case/cr_isoP=> bijf ef /CRStr2.cr_autoP [] bijg eg; apply/cr_isoP.
      by split; [apply/bij_comp|apply/cr_homo_endo_comp].
    qed.

    lemma cr_iso0 f :
      cr_iso f =>
      morphism_0 f RL1.zeror RL2.zeror.
    proof. by move/cr_iso_mono; apply/cr_mono0. qed.

    lemma cr_isoD f :
      cr_iso f =>
      morphism_2 f RL1.(+) RL2.(+).
    proof. by move/cr_iso_mono; apply/cr_monoD. qed.

    lemma cr_isoN f :
      cr_iso f =>
      morphism_1 f RL1.([-]) RL2.([-]).
    proof. by move/cr_iso_mono; apply/cr_monoN. qed.

    lemma cr_isoB f :
      cr_iso f =>
      morphism_2 f RL1.( - ) RL2.( - ).
    proof. by move/cr_iso_mono; apply/cr_monoB. qed.

    lemma cr_isoMz f :
      cr_iso f =>
      forall x n , f (RL1.intmul x n) = RL2.intmul (f x) n.
    proof. by move/cr_iso_mono; apply/cr_monoMz. qed.

    lemma cr_iso1 f :
      cr_iso f =>
      morphism_0 f RL1.oner RL2.oner.
    proof. by move/cr_iso_mono/cr_mono1. qed.
  
    lemma cr_isoM f :
      cr_iso f =>
      morphism_2 f RL1.( * ) RL2.( * ).
    proof. by move/cr_iso_mono/cr_monoM. qed.

    lemma cr_isoU f :
      cr_iso f =>
      forall x ,
        RL2.unit (f x) = RL1.unit x.
    proof.
      move=> ef x; apply/eq_iff; split; [|by apply/cr_monoUR/cr_iso_mono].
      move/cr_iso_bij: (ef) => [g] [] canfg cangf; rewrite !unitrP => -[y] eq_.
      by exists (g y); apply/(cr_iso_inj _ ef); rewrite cr_iso1 // cr_isoM // cangf.
    qed.
  
    lemma cr_isoV f :
      cr_iso f =>
      morphism_1 f RL1.invr RL2.invr.
    proof.
      move=> ef x; rewrite cr_monoVR ?cr_iso_mono //.
      by case (unit x) => // Nux; rewrite -eq_sym unitout // cr_isoU.
    qed.
  
    lemma cr_isoZ f :
      cr_iso f =>
      forall n , f (RL1.ofint n) = RL2.ofint n.
    proof. by move/cr_iso_mono/cr_monoZ. qed.
  
    lemma cr_isoX f :
      cr_iso f =>
      forall x n ,
        f (RL1.exp x n) =
        RL2.exp (f x) n.
    proof.
      move=> ef x n; rewrite cr_monoXR ?cr_iso_mono //.
      case (unit x) => // Nux; case (0 <= n) => [le0n|/ltrNge/ltzW len0].
      + by rewrite ger0_norm.
      by rewrite ler0_norm // -exprV unitout // cr_isoU.
    qed.

    lemma cr_iso_eq0 f :
      cr_iso f =>
      forall x , f x = RL2.zeror <=> x = RL1.zeror.
    proof. by move/cr_iso_mono; apply/cr_mono_eq0. qed.

    lemma cr_iso_order f :
      cr_iso f =>
      forall x , ZModStr2.order (f x) = ZModStr1.order x.
    proof. by move/cr_iso_zmod/zmod_iso_order. qed.

    lemma cr_iso_orbit f :
      cr_iso f =>
      forall x y ,
        orbit (f x) (f y) = orbit x y.
    proof. by move/cr_iso_zmod/zmod_iso_orbit. qed.
  
    lemma cr_iso_orbit_list f :
      cr_iso f =>
      forall x ,
        orbit_list (f x) = map f (orbit_list x).
    proof. by move/cr_iso_zmod/zmod_iso_orbit_list. qed.
  
    lemma cr_iso_eqv_orbit f :
      cr_iso f =>
      forall x y z ,
        eqv_orbit (f x) (f y) (f z) =
        eqv_orbit x y z.
    proof. by move/cr_iso_zmod/zmod_iso_eqv_orbit. qed.

    lemma subcr_subcr_cr_iso f P :
      cr_iso f =>
      CRStr2.subcr P =>
      subcr (P \o f).
    proof. by move/cr_iso_mono/subcr_subcr_cr_mono/(_ P). qed.

    lemma subcr_cr_iso_subcr f P :
      cr_iso f =>
      CRStr1.subcr P =>
      subcr (fun y => exists x , f x = y /\ P x).
    proof. by move/cr_iso_mono/subcr_cr_mono_subcr/(_ P). qed.

    lemma cr_iso_char f :
      cr_iso f =>
      CRStr1.char = CRStr2.char.
    proof. by move=> ef; rewrite /char -(cr_iso1 _ ef) cr_iso_order. qed.
  end CRMorph.
end ComRingMorph.

(* -------------------------------------------------------------------- *)
theory IDomainMorph.
  type t1, t2.

  clone include IDomainStruct with
    type t <- t1
    rename [theory] "RL"  as "RL1"
    rename [theory] "Str" as "Str1".

  clone include IDomainStruct with
    type t <- t2
    rename [theory] "RL"  as "RL2"
    rename [theory] "Str" as "Str2".

  clone include ComRingMorph with
    type t1 <- t1,
    type t2 <- t2,
    theory RL1 <- RL1,
    theory RL2 <- RL2,
    theory ZModStr1 <- ZModStr1,
    theory ZModStr2 <- ZModStr2,
    theory CRStr1 <- CRStr1,
    theory CRStr2 <- CRStr2
    rename [theory] "RL"  as "Gone"
           [theory] "Str" as "Gone".

  theory IDMorph.
    import RL1 RL2 ZModStr1 ZModStr2 CRStr1 CRStr2 IDStr1 IDStr2 ZModMorph CRMorph.

    lemma cr_homo_char_integral f :
      cr_homo f =>
      (CRStr1.char = 0 /\ prime CRStr2.char) \/ CRStr1.char = CRStr2.char.
    proof.
      move=> ef; move: IDStr1.char_integral IDStr2.char_integral (cr_homo_char _ ef).
      case=> [eq1|p1]; (case=> [eq2|p2]).
      + by rewrite eq1 eq2.
      + by rewrite eq1 p2.
      + by rewrite eq2 => /dvd0z ->.
      case/(prime_dvd _ _ p1 CRStr2.ge0_char) => [|-> //] eq_.
      by move: p2; rewrite eq_ => /gt1_prime.
    qed.

    lemma cr_homo_frobenius f :
      cr_homo f =>
      (CRStr1.char = 0 => CRStr2.char = 0) =>
      forall x ,
        f (IDStr1.frobenius x) = frobenius (f x).
    proof.
      rewrite /frobenius => ef imp_ x; rewrite cr_homoXR // ger0_norm ?ge0_char //.
      rewrite if_same; move: (cr_homo_char_integral _ ef) imp_.
      by case=> [[] -> _ /= ->|->].
    qed.

    lemma cr_homo_iter_frobenius_fixed f :
      cr_homo f =>
      (CRStr1.char = 0 => CRStr2.char = 0) =>
      forall n x ,
        IDStr1.iter_frobenius_fixed n x =>
        IDStr2.iter_frobenius_fixed n (f x).
    proof.
      rewrite /iter_frobenius_fixed => ef imp_ n x; case: (0 <= n) => [le0n|/ltrNge/ltzW len0].
      + rewrite !iter_frobenius //; move: (cr_homoXR _ ef x (CRStr2.char ^ n)).
        rewrite ger0_norm ?expr_ge0 ?ge0_char // if_same => <-.
        move: (cr_homo_char_integral _ ef) imp_.
        by case=> [[] -> _ /= ->|-> _] ->.
      by rewrite !iter0.
    qed.

    lemma cr_mono_frobenius f :
      cr_mono f =>
      forall x ,
        f (IDStr1.frobenius x) = IDStr2.frobenius (f x).
    proof.
      move=> ef; move/cr_mono_homo/cr_homo_frobenius: (ef).
      by rewrite (CRMorph.cr_mono_char _ ef).
    qed.

    lemma cr_mono_iter_frobenius_fixed f :
      cr_mono f =>
      forall n x ,
        IDStr2.iter_frobenius_fixed n (f x) =
        IDStr1.iter_frobenius_fixed n x.
    proof.
      move=> ef; move/cr_mono_homo/cr_homo_iter_frobenius_fixed: (ef).
      rewrite (CRMorph.cr_mono_char _ ef) /= => + n x; move/(_ n x) => imp_.
      apply/eq_iff; split=> //; rewrite /iter_frobenius_fixed.
      case: (0 <= n) => [le0n|/ltrNge/ltzW len0].
      + rewrite IDStr1.iter_frobenius // IDStr2.iter_frobenius //.
        move: (cr_monoXR _ ef x (CRStr2.char ^ n)).
        rewrite ger0_norm ?expr_ge0 ?ge0_char // if_same => <-.
        rewrite (CRMorph.cr_mono_char _ ef).
        by apply/(cr_mono_inj _ ef).
      by rewrite !iter0.
    qed.

    lemma cr_iso_frobenius f :
      cr_iso f =>
      forall x ,
        f (IDStr1.frobenius x) = frobenius (f x).
    proof. by move/cr_iso_mono/cr_mono_frobenius. qed.

    lemma cr_iso_iter_frobenius_fixed f :
      cr_iso f =>
      forall n x ,
        IDStr2.iter_frobenius_fixed n (f x) =
        IDStr1.iter_frobenius_fixed n x.
    proof. by move/cr_iso_mono/cr_mono_iter_frobenius_fixed. qed.
  end IDMorph.
end IDomainMorph.

(* -------------------------------------------------------------------- *)
theory FieldMorph.
  type t1, t2.

  clone include FieldStruct with
    type t <- t1
    rename [theory] "RL"  as "RL1"
    rename [theory] "Str" as "Str1".

  clone include FieldStruct with
    type t <- t2
    rename [theory] "RL"  as "RL2"
    rename [theory] "Str" as "Str2".

  clone include IDomainMorph with
    type t1 <- t1,
    type t2 <- t2,
    theory RL1 <- RL1,
    theory RL2 <- RL2,
    theory ZModStr1 <- ZModStr1,
    theory ZModStr2 <- ZModStr2,
    theory CRStr1 <- CRStr1,
    theory CRStr2 <- CRStr2,
    theory IDStr1 <- IDStr1,
    theory IDStr2 <- IDStr2
    rename [theory] "RL"  as "Gone"
           [theory] "Str" as "Gone".

  theory FMorph.
    import RL1 RL2 ZModStr1 ZModStr2 CRStr1 CRStr2 IDStr1 IDStr2 FStr1 FStr2.
    import ZModMorph CRMorph IDMorph.

    lemma cr_homoU f :
      cr_homo f =>
      forall x ,
        unit (f x) = unit x.
    proof.
      move=> ef x; apply/eq_iff; split; [|by apply/cr_homoUR].
      by rewrite -!unitfE; apply/implybNN => ->>; apply/cr_homo0.
    qed.
  
    lemma cr_homoV f :
      cr_homo f =>
      morphism_1 f RL1.invr RL2.invr.
    proof.
      move=> ef x; rewrite cr_homoVR //; case (unit x) => //.
      by rewrite -(cr_homoU _ ef) => Nu_; rewrite unitout.
    qed.
  
    lemma cr_homoX f :
      cr_homo f =>
      forall x n ,
        f (RL1.exp x n) =
        RL2.exp (f x) n.
    proof.
      move=> ef x n; rewrite cr_homoXR //; case (unit x) => //.
      case (0 <= n) => [le0n|/ltrNge/ltzW len0].
      + by rewrite ger0_norm.
      by rewrite ler0_norm // -exprV -(cr_homoU _ ef) => Nu_; rewrite unitout.
    qed.

    lemma cr_monoU f :
      cr_mono f =>
      forall x ,
        unit (f x) = unit x.
    proof. by move/cr_mono_homo/cr_homoU. qed.
  
    lemma cr_monoV f :
      cr_mono f =>
      morphism_1 f RL1.invr RL2.invr.
    proof. by move/cr_mono_homo/cr_homoV. qed.
  
    lemma cr_monoX f :
      cr_mono f =>
      forall x n ,
        f (RL1.exp x n) =
        RL2.exp (f x) n.
    proof. by move/cr_mono_homo/cr_homoX. qed.

    lemma cr_isoU f :
      cr_iso f =>
      forall x ,
        unit (f x) = unit x.
    proof. by move/cr_iso_mono/cr_monoU. qed.
  
    lemma cr_isoV f :
      cr_iso f =>
      morphism_1 f RL1.invr RL2.invr.
    proof. by move/cr_iso_mono/cr_monoV. qed.
  
    lemma cr_isoX f :
      cr_iso f =>
      forall x n ,
        f (RL1.exp x n) =
        RL2.exp (f x) n.
    proof. by move/cr_iso_mono/cr_monoX. qed.

    lemma subf_subf_cr_homo f P :
      cr_homo f =>
      FStr2.subf P =>
      subf (P \o f).
    proof.
      move=> ef sP; rewrite /(\o); split.
      + by apply/subcr_subcr_cr_homo => //; apply/subf_cr.
      by move=> x; rewrite cr_homoV //; apply/subfV.
    qed.

    lemma subf_cr_homo_subf f P :
      cr_homo f =>
      FStr1.subf P =>
      subf (fun y => exists x , f x = y /\ P x).
    proof.
      move=> ef sP; split.
      + by apply/subcr_cr_homo_subcr => //; apply/FStr1.subf_cr.
      move=> ? [x] [] <<- Px; exists (invr x).
      by rewrite cr_homoV // subfV.
    qed.

    lemma subf_subf_cr_mono f P :
      cr_mono f =>
      FStr2.subf P =>
      subf (P \o f).
    proof. by move/cr_mono_homo/subf_subf_cr_homo/(_ P). qed.

    lemma subf_cr_mono_subf f P :
      cr_mono f =>
      FStr1.subf P =>
      subf (fun y => exists x , f x = y /\ P x).
    proof. by move/cr_mono_homo/subf_cr_homo_subf/(_ P). qed.

    lemma subf_subf_cr_iso f P :
      cr_iso f =>
      FStr2.subf P =>
      subf (P \o f).
    proof. by move/cr_iso_mono/subf_subf_cr_mono/(_ P). qed.

    lemma subf_cr_iso_subf f P :
      cr_iso f =>
      FStr1.subf P =>
      subf (fun y => exists x , f x = y /\ P x).
    proof. by move/cr_iso_mono/subf_cr_mono_subf/(_ P). qed.
  end FMorph.
end FieldMorph.

