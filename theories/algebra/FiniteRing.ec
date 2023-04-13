(* ==================================================================== *)
require import AllCore List Ring Int IntMin IntDiv RingStruct Finite.
require import FinType ZModP UnitRing.
require import Bigalg SubRing RingModule Real RealExp Quotient Counting.
require (*--*) Subtype.
(*---*) import StdOrder.IntOrder.


(* ==================================================================== *)
abstract theory SubFinite.
  type t, st.

  clone import FinType as TFT with
    type t <= t.

  (*TODO: Pierre-Yves: this is needed because P is a pred in Sub and
                       must be used as an op in filter.
                       we need to replace pred by op everywhere in the StdLib*)
  op P : t -> bool.

  clone import Subtype as Sub with
    type T  <= t ,
    type sT <= st,
    pred P  <= P.

  import Sub.

  clone import FinType as SFT with
    type t  <= st,
    op enum <= map insubd (filter P enum)
  proof *.

  realize enum_spec.
  proof.
    move => x; rewrite /senum count_map count_filter /predI /preim.
    rewrite -(enum_spec (val x)); apply/eq_count.
    move => y; rewrite /pred1 /=; split => [[<<- in_sub_y]|->>].
    + by rewrite val_insubd in_sub_y.
    by rewrite valKd /= valP.
  qed.
end SubFinite.


(* ==================================================================== *)
abstract theory FiniteZModule.
  clone include ZModuleStruct.

  clone import FinType.FinType as FT with
    type t <= t.

  theory FZMod.
    import RL ZModStr FT.

    lemma gt0_order x :
      0 < order x.
    proof.
      case/ler_eqVlt: (ge0_order x) => // /eq_sym /order0P => inj_intmul.
      by have //: false; move: inj_intmul => /=; apply/not_injective_int.
    qed.
  
    import StdBigop.Bigint.
  
    lemma dvd_order_card x :
      order x %| FT.card.
    proof.
      have /(_ FT.enum):
        forall s , exists c ,
          uniq c /\
          (forall y z , y \in c => z \in c => eqv_orbit x y z => y = z) /\
          (mem s <= mem (flatten (map (fun y => map (RL.(+) y) (orbit_list x)) c))).
      + elim => [|y s [c] IHs]; [by exists [] => /=; rewrite flatten_nil|].
        move: IHs; pose l:= flatten _; case (y \in l) => [mem_y|Nmem_y];
        move => [uniq_ [forall_ mem_incl]].
        - by exists c; split => //; split => // z /= [->>|]; [apply/mem_y|apply/mem_incl].
        exists (y :: c); do!split => // [|z t|z] /=; [|move => [->>|mem_z] [->>|mem_t] //|].
        - move: Nmem_y; apply/contra; rewrite /l => {l mem_incl} mem_y; apply/flatten_mapP.
          exists y; split => //=; apply/mapP; exists zeror; rewrite addr0 /=.
          by apply/orbit_listP; rewrite ?gt0_order // orbit0.
        - rewrite /eqv_orbit orbit_listP ?gt0_order //; move: Nmem_y; rewrite /l -flatten_mapP.
          rewrite negb_exists => /= /(_ t); rewrite mem_t /= mapP negb_exists /= => /(_ (y - t)).
          by rewrite addrA addrAC subrr /= add0r.
        - rewrite eqv_orbit_sym /eqv_orbit orbit_listP ?gt0_order //.
          move: Nmem_y; rewrite /l -flatten_mapP.
          rewrite negb_exists => /= /(_ z); rewrite mem_z /= mapP negb_exists /= => /(_ (y - z)).
          by rewrite addrA addrAC subrr /= add0r.
        - by apply/forall_.
        rewrite flatten_cons -/l mem_cat; case => [->>|?]; [left|by right; apply/mem_incl].
        apply/mapP; exists zeror; rewrite addr0 /=.
        by apply/orbit_listP; rewrite ?gt0_order // orbit0.
      case => c; pose l:= flatten _; move => [uniq_ [forall_ mem_incl]].
      rewrite /card (perm_eq_size _ l).
      + apply/uniq_perm_eq; [by apply/FT.enum_uniq| |]; last first.
        - by move => ?; split; [apply/mem_incl|move => _; apply/FT.enumP].
        rewrite /l => {mem_incl l}; apply/uniq_flatten_map => //.
        - move => y /=; rewrite map_inj_in_uniq; [by move => ? ? _ _; apply/addrI|].
          by apply/uniq_orbit_list.
        move => y z mem_y mem_z /= /hasP [?] [] /mapP [t] [mem_t ->>] /mapP [u] [mem_u].
        move=> eq_.
        apply/forall_ => //; move: eq_; rewrite /eqv_orbit addrC -eqr_sub => <-.
        by apply/orbitB; apply/orbit_listP => //; apply/gt0_order.
      rewrite /l size_flatten sumzE (BIA.eq_big_seq _ (fun _ => order x)) /=.
      + move => ? /mapP [?] [+ ->>]; move => /mapP [?] /= [_ ->>].
        by rewrite size_map size_orbit_list.
      by rewrite BIA.sumr_const count_predT !size_map intmulz; apply/dvdz_mulr/dvdzz.
    qed.
  
    lemma isgeneratorP g :
      is_generator g <=> order g = card.
    proof.
      rewrite /is_generator -size_orbit_list; split => [orbit_|].
      + apply/perm_eq_size/uniq_perm_eq; [by apply/uniq_orbit_list|by apply/enum_uniq|].
        by move => x; rewrite -orbit_listP ?gt0_order // orbit_ enumP.
      move => eq_ x; move: (uniq_leq_size_perm_eq (orbit_list g) enum).
      rewrite orbit_listP ?gt0_order // uniq_orbit_list enum_uniq eq_ /card /= => /(_ _).
      + by move => ? _; apply/enumP.
      by move/perm_eq_mem => ->; apply/enumP.
    qed.
  
    op eq_order d x = order x = d.
  
    lemma few_small_order_exists_generator :
      (forall d , 0 <= d => d %| card =>
        size (to_seq (fun x => RL.intmul x d = zeror)) <= d) =>
      exists g , is_generator g.
    proof.
      move => forall_.
      have: forall d , 0 <= d => d %| card => size (to_seq (eq_order d)) <= phi (d).
      + move => d /ler_eqVlt [<<- _|lt0d dvdd_]; [rewrite phi_eq0 //|].
        - apply/size_le0/mem_eq0 => x; rewrite mem_to_seq; [by apply/is_finite_pred|].
          by rewrite /eq_order; apply/gtr_eqF/gt0_order.
        move: (size_ge0 (to_seq (eq_order d))).
        case /ler_eqVlt => [/eq_sym/size_eq0 ->/=|]; [by apply/phi_ge0|].
        rewrite -has_predT hasP => -[x] [mem_ _]; move: (sum_phi _ lt0d) => eq_d.
        move: (forall_ _ _ dvdd_); [by apply/ltzW|].
        move: mem_; rewrite mem_to_seq; [by apply/is_finite_pred|].
        move => eq_order_x; move: (size_orbit_list x); rewrite eq_order_x.
        move => eq_size_d; rewrite -{2}eq_size_d uniq_leq_size_perm_eq.
        - by apply/uniq_orbit_list.
        - by apply/uniq_to_seq.
        - move => ?; rewrite -orbit_listP ?gt0_order // => -[n] ->>.
          rewrite mem_to_seq /=; [by apply/is_finite_pred|].
          by rewrite -mulrM mulrC mulrM -eq_order_x intmul_order mul0i.
        move => eq_; move/perm_eq_size: eq_ (eq_); rewrite size_orbit_list eq_sym.
        move => eq_; move: eq_ (gt0_order x) => <-; rewrite ltrNge size_le0.
        pose P y := _ y _ = _; move => neq_; move: (to_seq_infinite P).
        move: neq_ => -> /=; rewrite /P => {P} is_finite_.
        move/(perm_eq_filter (eq_order d))/perm_eq_sym => eq_.
        move: (perm_eq_trans _ (to_seq (eq_order d)) _ _ eq_).
        - apply/uniq_perm_eq.
          * by apply/uniq_to_seq.
          * by apply/filter_uniq/uniq_to_seq.
          move => y; rewrite mem_to_seq ?is_finite_pred // mem_filter.
          rewrite -{1}(andbT (eq_order _ _)); apply/andb_id2l.
          rewrite eq_sym eqT => eq_order_y; rewrite mem_to_seq //=.
          by rewrite -eq_order_y; apply/intmul_order.
        move/perm_eq_size => ->; apply/lerr_eq; rewrite /phi.
        rewrite -(size_map (intmul x)); apply/perm_eq_size/uniq_perm_eq.
        - by apply/filter_uniq/uniq_orbit_list.
        - rewrite map_inj_in_uniq; [|by apply/coprimes_uniq].
          move => y z /coprimesP [copdy memy] /coprimesP [copdz memz].
          move/dvd2_order; rewrite -(IntID.subr_add2r (-1)) => /eq_mod.
          rewrite !modz_small ?gtr0_norm ?gt0_order //
            ?eq_order_x -?mem_range ?mem_range_subr //.
          by apply/IntID.addIr.
        move => y; rewrite mem_filter !mapP /=; split => [[eq_order_z] [z] [+ ->>]|].
        - rewrite range_iota /= => mem_; exists ((z - 1) %% d + 1); rewrite -eq_order_x.
          rewrite mulrSz intmul_modz_order -mulrSz /=; apply/coprimesP.
          rewrite mem_range_addr /=; split; last first.
          * by rewrite -{1}(gtr0_norm _ (gt0_order x)); apply/mem_range_mod/gtr_eqF/gt0_order.
          case/ltzE/ler_eqVlt: (gt0_order x) => [<-|gt1_orderx]; [by apply/coprime1z|].
          rewrite modz_small /=.
          * apply/mem_range; rewrite gtr0_norm ?gt0_order //; apply/mem_range_subr => /=.
            move: mem_; rewrite range_ltn ?gt0_order //=; case => [->>|]; last first.
            + by apply/mem_range_incl => //; apply/ltzW/ltzS.
            move: eq_order_z eq_order_x; rewrite mulr0z /eq_order order0 => <<-.
            by rewrite gtr_eqF.
          move: eq_order_z; rewrite /eq_order order_intmul ?gt0_order // -eq_order_x.
          rewrite -eqz_mul ?gcd_eq0 //=.
          * by apply/negb_and; rewrite gtr_eqF //; apply/gt0_order.
          rewrite eq_sym -subr_eq0 -mulN1r mulrC -mulrDl mulf_eq0 subr_eq0.
          by rewrite (gtr_eqF _ _ (gt0_order x)) /coprime.
        move => [z] [/coprimesP [coprimedz memz] ->>]; split.
        - by rewrite /eq_order order_intmul_coprime ?gt0_order // eq_order_x.
        exists (z %% d); rewrite range_iota /= -eq_order_x -{1}(gtr0_norm _ (gt0_order x)).
        by rewrite mem_range_mod ?gtr_eqF ?gt0_order //= intmul_modz_order.
      move => {forall_} forall_; move: (sum_phi _ card_gt0).
      move: (perm_eq_flatten_filter (fun d x => eq_order d x) enum (divisors card) _).
      + move => x _; rewrite count_filter; apply/count_eq1_eq; rewrite /predI.
        exists (order x) => /=; do!split.
        - apply/mem_range; rewrite -ltzS -ltr_subl_addr gt0_order /= ltzS.
          rewrite -(gtr0_norm (order _)) ?gt0_order // -(gtr0_norm card) ?card_gt0 //.
          by apply/dvdz_le; [apply/gtr_eqF/card_gt0|apply/dvd_order_card].
        - by apply/dvd_order_card.
        move => y; rewrite rem_filter ?range_uniq //.
        by rewrite mem_filter /predC1 /eq_order eq_sym; case => ->.
      move/perm_eq_size; rewrite {3}/card => ->; rewrite size_flatten sumzE.
      rewrite !BIA.big_mapT; move/lerr_eq => le_; move: (ler_ge_sum_eq_seq _ _ _ _ _ le_).
      + move => d /divisorsP [dvdd_ memd] _; rewrite /(\o) /=; move: (forall_ _ _ dvdd_).
        - by move:memd; apply/mem_range_le.
        apply/ler_trans/lerr_eq/perm_eq_size/uniq_perm_eq.
        - by apply/filter_uniq/enum_uniq.
        - by apply/uniq_to_seq.
        move => x; rewrite mem_filter /= mem_to_seq; [by apply/is_finite_pred|].
        by rewrite enumP.
      move => /(_ card _ _).
      + by apply/divisors_id/card_gt0.
      + by rewrite /predT.
      rewrite /(\o) /= => eq_; move: (phi_gt0 card _).
      + by apply/ltzS/ltr_subl_addr/card_gt0.
      move: eq_ => <- /has_predT; rewrite has_filter predTI => /hasP [g] [_] /= eq_.
      by exists g; apply/isgeneratorP; move: eq_; rewrite /eq_order.
    qed.
  end FZMod.
end FiniteZModule.

(* -------------------------------------------------------------------- *)
abstract theory FiniteComRing.
  clone include ComRingStruct.

  clone include FiniteZModule with
    type t         <- t,
    theory RL      <- RL,
    theory ZModStr <- ZModStr
    rename [theory] "RL"  as "Gone"
                    "Str" as "Gone".

  theory FCR.
    import FT RL ZModStr CRStr FZMod.

    lemma card_gt1: 1 < FT.card.
    proof.
      rewrite /card ltzE /=; have <-: size [RL.zeror; RL.oner] = 2 by trivial.
      apply/uniq_leq_size => //=; [by rewrite eq_sym; apply/RL.oner_neq0|].
      by move => ? _; apply/enumP.
    qed.

    lemma gt0_char :
      0 < char.
    proof. by rewrite /char; apply/gt0_order. qed.

    lemma gt1_char :
      1 < char.
    proof. by move/ltzE/ler_eqVlt: gt0_char; rewrite eq_sym /= neq1_char. qed.
  end FCR.
end FiniteComRing.

(* -------------------------------------------------------------------- *)
abstract theory FiniteIDomain.
  clone include IDomainStruct.

  clone include FiniteComRing with
    type t         <- t,
    theory RL      <- RL,
    theory ZModStr <- ZModStr,
    theory CRStr   <- CRStr
    rename [theory] "RL"  as "Gone"
                    "Str" as "Gone".

  theory FID.
    import FT RL ZModStr CRStr IDStr FZMod FCR.

    lemma prime_char :
      prime char.
    proof. by case: char_integral => // eq0; move: gt0_char; rewrite eq0. qed.
  
    lemma frobenius_surj :
      surjective frobenius.
    proof.
      move: (frobenius_inj prime_char) => inj_ x.
      move: (uniq_map_injective _ _ inj_ enum_uniq) => uniq_.
      move: (uniq_leq_size_perm_eq _ _ uniq_ enum_uniq _).
      + by move => ? _; apply/enumP.
      rewrite size_map /= => /perm_eq_mem /(_ x); rewrite enumP /=.
      by move => /mapP [y] [_ ->>]; exists y.
    qed.
  
    lemma frobenius_bij :
      bijective frobenius.
    proof.
      by apply/bij_inj_surj; split; [apply/frobenius_inj/prime_char|apply/frobenius_surj].
    qed.
  
    lemma frobenius_cr_auto :
      cr_auto frobenius.
    proof.
      by split; [apply/frobenius_surj|apply/frobenius_cr_mono_endo/prime_char].
    qed.
  
    lemma cr_auto_iter_frobenius n :
      cr_auto (iter n frobenius).
    proof. by apply/cr_auto_iter/frobenius_cr_auto. qed.
  end FID.
end FiniteIDomain.

(* -------------------------------------------------------------------- *)
abstract theory FiniteField.
  clone include FieldStruct.

  clone include FiniteIDomain with
    type t         <- t,
    theory RL      <- RL,
    theory ZModStr <- ZModStr,
    theory CRStr   <- CRStr,
    theory IDStr   <- IDStr
    rename [theory] "RL"      as "Gone"
                    "ZModStr" as "Gone"
                    "CRStr"   as "Gone"
                    "IDStr"   as "FiniteFieldFiniteIDomainIDStrGone"
                    "FStr"    as "FiniteFieldFiniteIDomainFStrGone".

  clone include UZMod_Field with
    type t         <- t,
    theory RL      <- RL,
    theory ZModStr <- ZModStr,
    theory CRStr   <- CRStr,
    theory IDStr   <- IDStr,
    theory FStr    <- FStr
    rename [theory] "RL"      as "Gone"
                    "ZModStr" as "Gone"
                    "CRStr"   as "Gone"
                    "IDStr"   as "FiniteFieldUZMod_FieldIDStrGone"
                    "FStr"    as "FiniteFieldUZMod_FieldFStrGone".

  clone include FiniteZModule with
    type t         <- uz,
    theory RL      <- UZ,
    theory ZModStr <- UStr
    rename [theory] "RL"      as "Gone"
                    "ZModStr" as "Gone"
                    "FT"      as "FUT"
                    "FZMod"   as "FUZMod".

  theory FF.
    import FT RL ZModStr CRStr IDStr FStr FZMod FCR FID.
    import UZ UStr USub FUT FUZMod.
  
    lemma card_unit :
      FT.card = FUT.card + 1.
    proof.
      rewrite /card (perm_eq_size  _ _ (perm_to_rem _ _ (FT.enumP RL.zeror))) /=.
      rewrite addrC; congr; rewrite -(size_map USub.val); apply/perm_eq_size/uniq_perm_eq.
      + by apply/rem_uniq/FT.enum_uniq.
      + by apply/uniq_map_injective; [apply/USub.val_inj|apply/FUT.enum_uniq].
      move => x; case: (x = RL.zeror) => [->>|neqx0].
      + rewrite rem_filter ?FT.enum_uniq // mem_filter /predC1 /= mapP.
        rewrite negb_exists /= => u; rewrite FUT.enumP /= eq_sym.
        by apply/negP; move/(congr1 unit); rewrite valP unitr0.
      rewrite mem_rem_neq // 1?eq_sym // FT.enumP /=; apply/mapP.
      by exists (insubd x); rewrite FUT.enumP /= val_insubd unitfP.
    qed.
  
    lemma exists_generator :
      exists g, UStr.is_generator g.
    proof.
      apply/few_small_order_exists_generator => d.
      case/ler_eqVlt => [<<- /dvd0z|lt0d]; [by move => eq_; move: FUT.card_gt0; rewrite eq_|].
      move => dvdd_; move: (size_to_seq_eq_pow_1 _ lt0d); apply/ler_trans/lerr_eq.
      rewrite -(size_map USub.insubd); apply/perm_eq_size/uniq_perm_eq.
      + by apply/uniq_to_seq.
      + rewrite map_inj_in_uniq; [|by apply/uniq_to_seq].
        move => x y; rewrite !mem_to_seq ?FT.is_finite_pred //.
        move => eqx eqy /(congr1 USub.val); rewrite !USub.insubdK //.
        - by apply/(unitrX_neq0 _ d); [apply/gtr_eqF|rewrite eqx unitr1].
        by apply/(unitrX_neq0 _ d); [apply/gtr_eqF|rewrite eqy unitr1].
      move => x; rewrite mapP mem_to_seq ?FUT.is_finite_pred //=.
      rewrite /eq_pow_1; split => [eq_|[y] [+ ->>]].
      + exists (USub.val x); rewrite USub.valKd /= mem_to_seq ?FT.is_finite_pred //=.
        by rewrite -UZModCR.valX eq_ val_insubd unitr1.
      rewrite mem_to_seq ?FT.is_finite_pred //= => eq_.
      apply/USub.val_inj; rewrite UZModCR.valX UZModCR.val1 USub.insubdK //.
      by apply/(unitrX_neq0 _ d); [apply/gtr_eqF|rewrite eq_ unitr1].
    qed.
  end FF.
end FiniteField.

(* ==================================================================== *)
abstract theory SubFiniteZModule.
  type t.

  op P : t -> bool.

  clone include SubZModule with
    type t <- t,
    pred Sub.P <= P.

  clone include SubFinite with
    type t     <- t,
    type st    <- st,
    op P       <- P,
    theory Sub <- Sub
    rename [theory] "Sub" as "Gone".

  clone include FiniteZModule with
    type t         <- t,
    theory RL      <- TRL,
    theory ZModStr <- ZModTStr,
    theory FT      <- TFT
    rename [theory] "FZMod" as "FZModT".

  clone include FiniteZModule with
    type t         <- st,
    theory RL      <- SRL,
    theory ZModStr <- ZModSStr,
    theory FT      <- SFT
    rename [theory] "FZMod" as "FZModS".
end SubFiniteZModule.

(* -------------------------------------------------------------------- *)
abstract theory SubFiniteComRing.
  type t.

  op P : t -> bool.

  clone include SubComRingModule with
    type t <- t,
    pred Sub.P <= P.

  clone include SubFiniteZModule with
    type t           <- t,
    type st          <- st,
    op P             <- P,
    theory TRL       <- TRL,
    theory SRL       <- SRL,
    theory ZModTStr  <- ZModTStr,
    theory ZModSStr  <- ZModSStr,
    theory ZModMorph <- ZModMorph,
    theory SZMod     <- SZMod,
    theory Sub       <- Sub
    rename [theory] "TRL"   as "Gone"
                    "SRL"   as "Gone"
                    "Str"   as "Gone"
                    "Morph" as "Gone"
                    "SZMod" as "Gone"
                    "Sub"   as "Gone".

  clone include FiniteComRing with
    type t         <- t,
    theory RL      <- TRL,
    theory ZModStr <- ZModTStr,
    theory CRStr   <- CRTStr,
    theory FT      <- TFT,
    theory FZMod   <- FZModT
    rename [theory] "FZMod" as "Gone"
                    "FCR"   as "FCRT".

  clone include FiniteComRing with
    type t         <- st,
    theory RL      <- SRL,
    theory ZModStr <- ZModSStr,
    theory CRStr   <- CRSStr,
    theory FT      <- SFT,
    theory FZMod   <- FZModS
    rename [theory] "FZMod" as "Gone"
                    "FCR"   as "FCRS".

  theory SFCR.
    import TRL SRL ZModTStr ZModSStr CRTStr CRSStr ZModMorph CRMorph SZMod SCR Sub CRM.
    import TFT SFT.

    op enum_lin (vs : t list) =
      map
        (fun ss => lin ss vs)
        (foldr (allpairs (::)) [[]] (nseq (size vs) SFT.enum)).
  
    lemma enum_lin_nil :
      enum_lin [] = [TRL.zeror].
    proof. by rewrite /enum_lin /= nseq0 /= BigMod.big_nil. qed.
  
    lemma enum_lin_cons v vs :
      enum_lin (v :: vs) =
      allpairs TRL.( + ) (map (transpose CRM.( ** ) v) SFT.enum) (enum_lin vs).
    proof.
      rewrite /enum_lin /= addrC nseqS ?size_ge0 //=; pose el := foldr _ _ _.
      elim: SFT.enum el => [|x senum IHsenum] el /=; [by rewrite !allpairs0l|].
      rewrite !allpairs_consl map_cat IHsenum -!map_comp; congr => {IHsenum}.
      by apply/eq_map => xs; rewrite /(\o) /= BigMod.big_cons /predT /idfun.
    qed.
  
    lemma enum_linP vs v :
      (v \in enum_lin vs) <=> (gen (vf_oflist vs) v).
    proof.
      elim: vs v => [|v vs IHvs] w.
      + by rewrite enum_lin_nil gen_vf_oflist_nil.
      rewrite enum_lin_cons gen_vf_oflist_cons allpairsP; split.
      + case => -[v1 v2] /= |> /mapP [s] |> mem_s /IHvs gen_v2.
        by exists s SRL.oner v2; rewrite gen_v2 scale1r.
      case => [s1 s2 w2] /= |> /(gen_scale _ s2) /IHvs mem_w2.
      exists (s1 ** v, s2 ** w2)%CRM; rewrite mem_w2 /=.
      split; last by rewrite /CRM.( ** ).
      by apply/mapP; exists s1 => /=; apply/SFT.enumP.
    qed.
  
    lemma size_enum_lin vs :
      size (enum_lin vs) = SFT.card ^ (size vs).
    proof.
      elim: vs => [|v vs IHvs] /=.
      + by rewrite expr0 enum_lin_nil.
      rewrite addrC exprS ?size_ge0 // -IHvs => {IHvs}.
      rewrite /enum_lin !size_map /= addrC nseqS ?size_ge0 //=.
      by rewrite size_allpairs -/SFT.card.
    qed.
  
    lemma free_uniq_enum_lin vs :
      uniq vs =>
      free (vf_oflist vs) =>
      uniq (enum_lin vs).
    proof.
      elim: vs => [|v vs IHvs]; [by rewrite enum_lin_nil|].
      rewrite free_vf_oflist_cons enum_lin_cons /=.
      move => |> Nmem_v uniq_ imp_eq0 free_.
      rewrite allpairs_mapl; apply/allpairs_uniq.
      + by apply/SFT.enum_uniq.
      + by apply/IHvs.
      move => s1 s2 v1 v2 mem_s1 mem_s2 /enum_linP gen1 /enum_linP gen2 /=.
      rewrite addrC -eqr_sub -scaleNr -scaleDl => eq_.
      move/(_ (s2 + (-s1))%SRL _): imp_eq0.
      + by rewrite -eq_; apply/gen_add => //; apply/gen_opp.
      rewrite SRL.subr_eq0 => ->>; move: eq_.
      by rewrite /= SRL.subrr scale0r TRL.subr_eq0.
    qed.
  
    lemma gen_t_enum_lin vs :
      (gen_t (vf_oflist vs)) <=> (forall v , v \in enum_lin vs).
    proof. by rewrite /gen_t; apply/forall_eq => v /=; apply/eqboolP; rewrite enum_linP. qed.
  end SFCR.
end SubFiniteComRing.

(* -------------------------------------------------------------------- *)
abstract theory SubFiniteIDomain.
  type t.

  op P : t -> bool.

  clone include SubIDomainModule with
    type t <- t,
    pred Sub.P <= P.

  clone include SubFiniteComRing with
    type t           <- t,
    type st          <- st,
    op P             <- P,
    theory TRL       <- TRL,
    theory SRL       <- SRL,
    theory ZModTStr  <- ZModTStr,
    theory ZModSStr  <- ZModSStr,
    theory CRTStr    <- CRTStr,
    theory CRSStr    <- CRSStr,
    theory ZModMorph <- ZModMorph,
    theory CRMorph   <- CRMorph,
    theory SZMod     <- SZMod,
    theory SCR       <- SCR,
    theory CRM       <- CRM,
    theory Sub       <- Sub
    rename [theory] "TRL"   as "Gone"
                    "SRL"   as "Gone"
                    "Str"   as "Gone"
                    "Morph" as "Gone"
                    "SZMod" as "Gone"
                    "SCR"   as "Gone"
                    "CRM"   as "Gone"
                    "Sub"   as "Gone".

  clone include FiniteIDomain with
    type t         <- t,
    theory RL      <- TRL,
    theory ZModStr <- ZModTStr,
    theory CRStr   <- CRTStr,
    theory IDStr   <- IDTStr,
    theory FT      <- TFT,
    theory FZMod   <- FZModT,
    theory FCR     <- FCRT
    rename [theory] "FZMod" as "Gone"
                    "FCR"   as "Gone"
                    "FID"   as "FIDT"
                    "IDStr" as "FiniteIDomainTIDStrGone".

  clone include FiniteIDomain with
    type t         <- st,
    theory RL      <- SRL,
    theory ZModStr <- ZModSStr,
    theory CRStr   <- CRSStr,
    theory IDStr   <- IDSStr,
    theory FT      <- SFT,
    theory FZMod   <- FZModS,
    theory FCR     <- FCRS
    rename [theory] "FZMod" as "Gone"
                    "FCR"   as "Gone"
                    "FID"   as "FIDS"
                    "IDStr" as "FiniteIDomainSIDStrGone".
end SubFiniteIDomain.

(* -------------------------------------------------------------------- *)
abstract theory SubFiniteField.
  type t.

  op P : t -> bool.

  clone include SubVectorSpace with
    type t <- t,
    pred Sub.P <= P.

  clone include SubFiniteIDomain with
    type t           <- t,
    type st          <- st,
    op P             <- P,
    theory TRL       <- TRL,
    theory SRL       <- SRL,
    theory ZModTStr  <- ZModTStr,
    theory ZModSStr  <- ZModSStr,
    theory CRTStr    <- CRTStr,
    theory CRSStr    <- CRSStr,
    theory IDTStr    <- IDTStr,
    theory IDSStr    <- IDSStr,
    theory ZModMorph <- ZModMorph,
    theory CRMorph   <- CRMorph,
    theory IDMorph   <- IDMorph,
    theory SZMod     <- SZMod,
    theory SCR       <- SCR,
    theory SID       <- SID,
    theory CRM       <- CRM,
    theory Sub       <- Sub
    rename [theory] "TRL"       as "Gone"
                    "SRL"       as "Gone"
                    "ZModTStr"  as "Gone"
                    "ZModSStr"  as "Gone"
                    "CRTStr"    as "Gone"
                    "CRSStr"    as "Gone"
                    "IDTStr"    as "SubFiniteFieldIDTStrGone"
                    "IDSStr"    as "SubFiniteFieldIDSStrGone"
                    "IDStr1"    as "SubFiniteFieldIDStr1Gone"
                    "IDStr2"    as "SubFiniteFieldIDStr2Gone"
                    "ZModMorph" as "Gone"
                    "CRMorph"   as "Gone"
                    "IDMorph"   as "SubFiniteFieldIDMorphGone"
                    "SZMod"     as "Gone"
                    "SCR"       as "Gone"
                    "SID"       as "Gone"
                    "CRM"       as "Gone"
                    "Sub"       as "Gone".

  clone include FiniteField with
    type t         <- t,
    theory RL      <- TRL,
    theory ZModStr <- ZModTStr,
    theory CRStr   <- CRTStr,
    theory IDStr   <- IDTStr,
    theory FStr    <- FTStr,
    theory FT      <- TFT,
    theory FZMod   <- FZModT,
    theory FCR     <- FCRT,
    theory FID     <- FIDT
    rename [theory] "FZMod" as "Gone"
                    "FCR"   as "Gone"
                    "FID"   as "Gone"
                    "FF"    as "FFT"
                    "IDStr" as "FiniteFieldTIDStrGone"
                    "FStr"  as "FiniteFieldTFStrGone"
                    "UZ"    as "UZT"
                    "UStr"  as "UTStr"
                    "UFZMod" as "UFZModT"
                    "USub"  as "USubT"
                    "FUT"   as "FUTT"
           [type]   "uz"    as "uzt".

  clone include FiniteField with
    type t         <- st,
    theory RL      <- SRL,
    theory ZModStr <- ZModSStr,
    theory CRStr   <- CRSStr,
    theory IDStr   <- IDSStr,
    theory FStr    <- FSStr,
    theory FT      <- SFT,
    theory FZMod   <- FZModS,
    theory FCR     <- FCRS,
    theory FID     <- FIDS
    rename [theory] "FZMod" as "Gone"
                    "FCR"   as "Gone"
                    "FID"   as "Gone"
                    "FF"    as "FFS"
                    "IDStr" as "FiniteFieldSIDStrGone"
                    "FStr"  as "FiniteFieldSFStrGone"
                    "UZ"    as "UZS"
                    "UStr"  as "USStr"
                    "USub"  as "USubS"
                    "FUT"   as "FUTS"
           [type]   "uz"    as "uzs".

  theory SFF.
    import TRL SRL ZModTStr ZModSStr CRTStr CRSStr IDTStr IDSStr FTStr FSStr.
    import ZModMorph CRMorph IDMorph FMorph SZMod SCR SID SF Sub CRM.
    import TFT SFT SFCR.

    lemma finite_basis_exists :
      exists vs , uniq vs /\ basis (vf_oflist vs).
    proof.
      have /(_ TFT.card):
        forall n , 0 <= n => n <= TFT.card =>
        exists vs , uniq vs /\ free (vf_oflist vs) /\ n <= size (enum_lin vs);
      last first.
      + rewrite size_ge0 /= => -[vs] |> uniq_ free_ lecn.
        exists vs; rewrite uniq_ /basis free_ /= gen_t_enum_lin => v.
        move: lecn; rewrite uniq_leq_size_perm_eq.
        - by apply/free_uniq_enum_lin.
        - by apply/TFT.enum_uniq.
        - by move => ? _; apply/TFT.enumP.
        by move => /perm_eq_mem ->; apply/TFT.enumP.
      elim => [_|n le0n IHn /ltzE ltnc].
      + by exists []; rewrite free_vf_oflist_nil size_ge0.
      case/(_ _): IHn => [|vs |> uniq_ free_]; [by apply/ltzW|].
      move => /ler_eqVlt [->>|ltnp]; [|by exists vs; rewrite -ltzE].
      move/ltzNge: ltnc; rewrite uniq_leq_size_perm_eq.
      + by apply/free_uniq_enum_lin.
      + by apply/TFT.enum_uniq.
      + by move => ? _; apply/TFT.enumP.
      move => Nperm_eq_; move: (uniq_perm_eq (enum_lin vs) TFT.enum _ _).
      + by apply/free_uniq_enum_lin.
      + by apply/TFT.enum_uniq.
      rewrite Nperm_eq_ /= negb_forall /= => -[v]; rewrite TFT.enumP /= => Nmemv.
      exists (v :: vs); rewrite /= free_vf_oflist_cons uniq_ free_ /=; do!split.
      + by move: Nmemv; apply/contra => memv; apply/enum_linP/gen_p.
      + right => s; case: (s = SRL.zeror) => [->> //=|neqs0].
        rewrite -gen_scale_unit -?enum_linP //; apply/unitfP.
        by move: neqs0; apply/contra => ->>; apply/Sub.val_inj; rewrite val0.
      rewrite !size_enum_lin /= -ltzE addrC exprSr ?size_ge0 //.
      rewrite -subr_gt0 -IntID.mulN1r mulrC -IntID.mulrDl; apply/mulr_gt0.
      + by rewrite subr_gt0; apply/FCRS.card_gt1.
      by apply/expr_gt0/SFT.card_gt0.
    qed.
  
    op n = ilog SFT.card TFT.card.
  
    lemma lt0n :
      0 < n.
    proof.
      rewrite /n ltzE /=; move: (ilog_mono SFT.card SFT.card TFT.card).
      rewrite ilog_b FCRS.card_gt1 SFT.card_gt0 /= => -> //.
      by rewrite /SFT.card /TFT.card size_map size_filter count_size.
    qed.
  
    lemma eq_card_pow_n :
      TFT.card = SFT.card ^ n.
    proof.
      case: finite_basis_exists => vs [uniq_ basis_].
      case: (basis_) => free_ /gen_t_enum_lin mem_e.
      move: (free_uniq_enum_lin _ uniq_ free_) => uniq_e.
      move: (size_enum_lin vs); rewrite /n /SFT.card /TFT.card.
      rewrite (perm_eq_size _ TFT.enum).
      + apply/uniq_perm_eq => // [|x]; [by apply/TFT.enum_uniq|].
        by rewrite TFT.enumP mem_e.
      by move=> ->; rewrite ilog_powK // FCRS.card_gt1.
    qed.
  end SFF.
end SubFiniteField.


(* ==================================================================== *)
abstract theory ZModP_FiniteField.
  type t.

  op p : int.

  axiom prime_p : prime p.

  clone import ZModField as ZModP with
    type zmod     <= t,
    op p          <= p,
    axiom prime_p <= prime_p.

  (*TODO: issue in ZModP: should be a clone with theory ZModP.ZModpField.*)
  clone import Field as F with
    type t          <= t,
    op zeror        <= ZModP.zero,
    op oner         <= ZModP.one,
    op (+)          <= ZModP.(+),
    op [-]          <= ZModP.([-]),
    op ( * )        <= ZModP.( * ),
    op invr         <= ZModP.inv,
    pred unit       <= ZModP.unit,
    lemma addrA     <= ZModP.ZModpField.addrA,
    lemma addrC     <= ZModP.ZModpField.addrC,
    lemma add0r     <= ZModP.ZModpField.add0r,
    lemma addNr     <= ZModP.ZModpField.addNr,
    lemma oner_neq0 <= ZModP.ZModpField.oner_neq0,
    lemma mulrA     <= ZModP.ZModpField.mulrA,
    lemma mulrC     <= ZModP.ZModpField.mulrC,
    lemma mul1r     <= ZModP.ZModpField.mul1r,
    lemma mulrDl    <= ZModP.ZModpField.mulrDl,
    lemma mulVr     <= ZModP.ZModpField.mulVr,
    lemma unitP     <= ZModP.ZModpField.unitP,
    lemma unitout   <= ZModP.ZModpField.unitout,
    lemma mulf_eq0  <= ZModP.ZModpField.mulf_eq0.

  clone import FiniteField as FF with
    type t          <= t,
    theory F        <= F,
    op FinType.enum <= map inzmod (range 0 p)
    proof *.

  realize FinType.enum_spec.
  proof.
    move => x; rewrite count_uniq_mem ?b2i_eq1.
    + rewrite map_inj_in_uniq ?range_uniq // => m n range_m range_n /eq_inzmod.
      by rewrite !modz_small -?mem_range ?gtr0_norm ?gt0_prime ?prime_p.
    by apply/mapP; exists (asint x); rewrite asintK /=; apply/mem_range/rg_asint.
  qed.

  lemma eq_card_p :
    FinType.card = p.
  proof. by rewrite /FinType.card size_map size_range ler_maxr //=; apply/ltzW/gt0_prime/prime_p. qed.
end ZModP_FiniteField.


(* ==================================================================== *)
abstract theory SubFiniteField_ZMod.
  type t, ut, st.

  clone import Field as F with
    type t <= t.

  clone import FiniteField as FF with
    type t   <= t,
    theory F <= F.

  clone import FieldStruct as FStr with
    type t   <= t,
    theory F <= F.

  clone import FiniteFieldStruct as FFStr with
    type t      <= t,
    type ut     <= ut,
    theory F    <= F,
    theory FStr <= FStr,
    theory FF   <= FF.

  clone import ZModField as ZModP with
    type zmod     <= st,
    op p          <= SubFiniteField_ZMod.FStr.char,
    axiom prime_p <= SubFiniteField_ZMod.FFStr.prime_char.

  clone import ZModP_FiniteField as ZModPFF with
    type t        <= st,
    op p          <= SubFiniteField_ZMod.FStr.char,
    axiom prime_p <= SubFiniteField_ZMod.FFStr.prime_char,
    theory ZModP  <= SubFiniteField_ZMod.ZModP.

  op is_ofint (x : t) n = (x = ofint n).

  op in_zmodP x = exists n , is_ofint x n.

  op insub (x : t) = 
    if in_zmodP x
    then Some (ZModpRing.ofint (argmin idfun (is_ofint x))) 
    else None.

  op val (x : st) = ofint (Sub.val x).

  op wsT = ofint (asint witness).

  clone import SubField as SF with
    type t       <= t,
    type st      <= st,
    theory F     <= SubFiniteField_ZMod.F,
    op p         <= in_zmodP,
    op Sub.insub <= insub,
    op Sub.val   <= val,
    op Sub.wsT   <= wsT
    proof *.

  realize fieldp.
  proof.
    rewrite /in_zmodP /is_ofint; do 3!split; [split| | |]; rewrite /=.
    + by exists 0; rewrite ofint0.
    + by move => x [nx] ->>; exists (-nx); rewrite ofintN.
    + by move => x y [nx] ->> [ny] ->>; exists (nx + ny); rewrite addrz.
    + by exists 1; rewrite ofint1.
    + by move => x y [nx] ->> [ny] ->>; exists (nx * ny); rewrite mulrz.
    move => x [nx] ->>; move: (mulmV _ nx prime_char).
    case: (nx %% char = 0) => /= [eq_0|_ eq_1].
    + by exists 0; move: (dvd_char nx); rewrite dvdzE eq_0 /= => ->; rewrite invr0 ofint0.
    exists (invm nx char); move: (dvdzE char (nx * invm nx char)); rewrite eq_1 /= => Ndvd.
    apply/(mulrI (ofint nx)).
    + by rewrite -unitfE -dvd_char; apply/negP => dvd_; apply/Ndvd/dvdz_mulr.
    rewrite mulrz divrr //.
    + by rewrite -unitfE -dvd_char; apply/negP => dvd_; apply/Ndvd/dvdz_mulr.
    rewrite eq_sym -ofint1 -dvd2_char dvdzE -modzDm eq_1 -{1}(modz_small 1 char).
    + by rewrite /= ltr_normr; left; apply/gt1_char.
    by rewrite modzDm.
  qed.

  realize Sub.insubN.
  proof. by rewrite /insub => x ->. qed.

  realize Sub.insubT.
  proof.
    rewrite /insub; move => x in_x; rewrite in_x /=.
    case: in_x => nx; rewrite /is_ofint => ->>.
    rewrite (argmin_eq _ _ (nx %% char)) //=.
    + by apply/modz_ge0/gtr_eqF/gt0_char.
    + by rewrite /idfun /= -dvd2_char -divzE dvdz_mull dvdzz.
    + move => j /mem_range mem_j_range; rewrite /idfun /=.
      rewrite -dvd2_char dvdzE; apply/gtr_eqF.
      move/mem_range: mem_j_range => [le0j ltj_].
      rewrite (divz_eq nx char) -addrA modzMDl modz_small; [|by apply/subr_gt0].
      rewrite subr_ge0 ltzW //= (ltr_le_sub _ `|char| _ 0) //.
      by apply/ltz_mod/gtr_eqF/gt0_char.
    rewrite /val -dvd2_char -/asint ofint_inzmod -inzmod_mod inzmodK.
    by rewrite -opprB dvdzN -divzE dvdz_mull dvdzz.
  qed.

  realize Sub.valP.
  proof. by rewrite /in_zmodP /val; move => x; exists (SubFiniteField_ZMod.ZModP.Sub.val x). qed.

  realize Sub.valK.
  proof.
    rewrite /pcancel /insub => x.
    have in_x: (in_zmodP (ofint (SubFiniteField_ZMod.ZModP.Sub.val x))).
    + by exists (SubFiniteField_ZMod.ZModP.Sub.val x).
    rewrite in_x /=; case: in_x => n is_ofint_.
    move: (argminP idfun (is_ofint (SubFiniteField_ZMod.val x)) (n %% char) _ _).
    + by apply/modz_ge0/gtr_eqF/gt0_char.
    + by rewrite /val /idfun /= is_ofint_ /is_ofint -dvd2_char -divzE dvdz_mull dvdzz.
    rewrite /val {1}/is_ofint /idfun /= => ?; rewrite (argmin_eq _ _ (n %% char)) /=.
    + by apply/modz_ge0/gtr_eqF/gt0_char.
    + by rewrite is_ofint_ /is_ofint -dvd2_char -divzE dvdz_mull dvdzz.
    + move => j /mem_range mem_j_range; rewrite /idfun /=.
      rewrite is_ofint_ /is_ofint -dvd2_char dvdzE; apply/gtr_eqF.
      move/mem_range: mem_j_range => [le0j ltj_].
      rewrite (divz_eq n char) -addrA modzMDl modz_small; [|by apply/subr_gt0].
      rewrite subr_ge0 ltzW //= (ltr_le_sub _ `|char| _ 0) //.
      by apply/ltz_mod/gtr_eqF/gt0_char.
    move: is_ofint_; rewrite -/asint /is_ofint ofint_inzmod -inzmod_mod.
    move/dvd2_char => dvd_; apply/asint_inj; rewrite inzmodK.
    rewrite eq_sym -(modz_small (asint x) char); [|by apply/eq_mod].
    by rewrite ger0_norm ?rg_asint // ge0_char.
  qed.

  realize Sub.insubW.
  proof.
    rewrite /insub /wsT ifT; [by exists (asint witness)|congr].
    rewrite ofint_inzmod; apply/asint_inj; rewrite inzmodK.
    rewrite (argmin_eq _ _ (asint witness)) //; [by apply/ge0_asint| |].
    + move => j /mem_range mem_j_range; rewrite /idfun /=.
      rewrite /is_ofint -dvd2_char dvdzE; apply/gtr_eqF.
      move/mem_range: mem_j_range => [le0j ltj_].
      rewrite (divz_eq (asint witness) char) -addrA modzMDl modz_small.
      - rewrite subr_ge0 ltzW //=.
        * by rewrite modz_small //; rewrite ger0_norm ?rg_asint // ge0_char.
        by rewrite (ltr_le_sub _ `|char| _ 0) //; apply/ltz_mod/gtr_eqF/gt0_char.
      by apply/subr_gt0; rewrite modz_small //; rewrite ger0_norm ?rg_asint // ge0_char.
    by rewrite modz_small //; rewrite ger0_norm ?rg_asint // ge0_char.
  qed.

  clone import SubFiniteField as SFF with
    type t       <= t,
    type ut      <= ut,
    type st      <= st,
    theory F     <= SubFiniteField_ZMod.F,
    theory FF    <= SubFiniteField_ZMod.FF,
    theory FStr  <= SubFiniteField_ZMod.FStr,
    theory FFStr <= SubFiniteField_ZMod.FFStr.

  lemma is_comringautomorph_exp f :
    is_comring_automorph f =>
    (exists k , 0 < k /\ forall x , f x = exp x k).
  proof.
    case: exists_generator => g isg_g iscra_f.
    move: (isg_g (SubFiniteField_ZMod.FFStr.UF.Sub.insubd (f (SubFiniteField_ZMod.FFStr.UF.Sub.val g)))).
    case => k eq_; exists (k %% SubFiniteField_ZMod.FFStr.SFU.SFT.card + SubFiniteField_ZMod.FFStr.SFU.SFT.card).
    apply/and_impr; split; [apply/ltzE/ler_add|].
    + by apply/modz_ge0/gtr_eqF/SFU.SFT.card_gt0.
    + by apply/ltzS/ltr_subl_addr/SFU.SFT.card_gt0.
    move => lt0_ x; case (SubFiniteField_ZMod.F.unit x) => [unitx|]; last first.
    + rewrite -SubFiniteField_ZMod.F.unitfE /= => ->>; rewrite comring_automorph0 //.
      by rewrite expr0z gtr_eqF.
    move/(congr1 UF.Sub.val): eq_; rewrite UF.Sub.insubdK.
    + apply/unitrE. rewrite -comring_automorphV // -comring_automorphM //.
      by rewrite divrr; [apply/UF.Sub.valP|apply/comring_automorph1].
    rewrite -UFStr.ZModStr.intmul_modz_order -modz_mod -modzDr UFStr.ZModStr.intmul_modz_order.
    move/UFStr.isgeneratorP: (isg_g) => ->; rewrite UF.val_intmul.
    case/(_ (UF.Sub.insubd x)): isg_g => i /(congr1 UF.Sub.val).
    rewrite UF.Sub.insubdK // UF.val_intmul => ->>.
    by rewrite comring_automorphX // => ->; rewrite -!exprM mulrC.
  qed.

  lemma is_comringautomorphP f :
    is_comring_automorph f <=>
    (exists k, k \in range 0 n /\ f == iter k frobenius).
  proof.
    split => [|[k] [_ /fun_ext ->>]]; last first.
    + by apply/is_comring_automorph_iter_frobenius.
    move => iscra_f.
    admit.
  qed.
end SubFiniteField_ZMod.
