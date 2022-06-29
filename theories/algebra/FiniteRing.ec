(* ==================================================================== *)
require import AllCore List Ring Int IntDiv RingStruct FinType ZModP.
require import Bigalg SubRing RingModule Real RealExp.
require (*--*) Subtype.
(*---*) import StdOrder.IntOrder.


(* ==================================================================== *)
abstract theory SubFinite.
  type t, st.

  op p : t -> bool.

  clone import FinType as FT with
    type t <= t.

  clone import Subtype as Sub with
    type T  <- t ,
    type sT <- st,
    pred P  <- p.

  import Sub.

  op senum = map insubd (filter p enum).

  clone import FinType as SFT with
    type t  <= st,
    op enum <- senum
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
  type t.

  clone import ZModule as ZMod with
    type t <= t.

  clone import FinType.FinType as FinType with
    type t <= t.
end FiniteZModule.

(* -------------------------------------------------------------------- *)
abstract theory FiniteComRing.
  type t.

  clone import ComRing as CR with
    type t <= t.

  clone include FiniteZModule with
    type t      <- t,
    theory ZMod <- CR.
end FiniteComRing.

(* -------------------------------------------------------------------- *)
abstract theory FiniteIDomain.
  type t.

  clone import IDomain as ID with
    type t <= t.

  clone include FiniteComRing with
    type t    <- t,
    theory CR <- ID.
end FiniteIDomain.

(* -------------------------------------------------------------------- *)
abstract theory FiniteField.
  type t.

  clone import Field as F with
    type t <= t.

  clone include FiniteIDomain with
    type t    <- t,
    theory ID <- F.
end FiniteField.


(* ==================================================================== *)
abstract theory FiniteZModuleStruct.
  type t.

  clone import ZModule as ZMod with
    type t <= t.

  clone import ZModuleStruct as ZModStr with
    type t      <= t,
    theory ZMod <- ZMod.

  clone import FiniteZModule as FZMod with
    type t      <= t,
    theory ZMod <- ZMod.

  lemma gt0_order x :
    0 < order x.
  proof.
    case/ler_eqVlt: (ge0_order x) => // /eq_sym /order0P => inj_intmul.
    by have //: false; move: inj_intmul => /=; apply/FinType.not_injective_int.
  qed.

  lemma dvd_order_card x :
    order x %| FinType.card.
  proof.
    admit.
  qed.
end FiniteZModuleStruct.

(* -------------------------------------------------------------------- *)
abstract theory FiniteComRingStruct.
  type t.

  clone import ComRing as CR with
    type t <= t.

  clone import ComRingStruct as CRStr with
    type t    <= t,
    theory CR <- CR.

  clone import FiniteComRing as FCR with
    type t    <= t,
    theory CR <- CR.

  clone include FiniteZModuleStruct with
    type t         <- t,
    theory ZMod    <- CR,
    theory ZModStr <- CRStr,
    theory FZMod   <- FCR.

  lemma gt0_char :
    0 < char.
  proof. by rewrite /char; apply/gt0_order. qed.

  lemma gt1_char :
    1 < char.
  proof. by move/ltzE/ler_eqVlt: gt0_char; rewrite eq_sym /= neq1_char. qed.
end FiniteComRingStruct.

(* -------------------------------------------------------------------- *)
abstract theory FiniteIDomainStruct.
  type t.

  clone import IDomain as ID with
    type t <= t.

  clone import IDomainStruct as IDStr with
    type t    <= t,
    theory ID <- ID.

  clone import FiniteIDomain as FID with
    type t    <= t,
    theory ID <- ID.

  clone include FiniteComRingStruct with
    type t       <- t,
    theory CR    <- ID,
    theory CRStr <- IDStr,
    theory FCR   <- FID.

  lemma prime_char : prime char.
  proof. by case: char_integral => // eq0; move: gt0_char; rewrite eq0. qed.
end FiniteIDomainStruct.

(* -------------------------------------------------------------------- *)
abstract theory FiniteFieldStruct.
  type t, ut.

  clone import Field as F with
    type t <= t.

  clone import FieldStruct as FStr with
    type t   <= t,
    theory F <- F.

  clone import FiniteField as FF with
    type t   <= t,
    theory F <- F.

  clone include FiniteIDomainStruct with
    type t       <- t,
    theory ID    <- F,
    theory IDStr <- FStr,
    theory FID   <- FF.

  clone import UZMod_Field as UF with
    type t   <- t,
    type uz  <- ut,
    theory F <- F.

  print UF.

  clone import SubFinite as SFU with
    type t    <- t,
    type st   <- ut,
    op p      <- (fun x => x <> zeror),
    theory FT <- FF.FinType.

  lemma card_unit :
    FF.FinType.card = SFU.SFT.card + 1.
  proof.
    rewrite /card (perm_eq_size  _ _ (perm_to_rem _ _ (FinType.enumP zeror))) /=.
    rewrite addrC; congr; rewrite -(size_map Sub.val); apply/perm_eq_size/uniq_perm_eq.
    + by apply/rem_uniq/FinType.enum_uniq.
    + by apply/uniq_map_injective; [apply/Sub.val_inj|apply/SFT.enum_uniq].
    move => x; case: (x = zeror) => [->>|neqx0].
    + rewrite /senum -map_comp; pose s:= filter _ _.
      case: (eq_in_map (Sub.val \o Sub.insubd) idfun s).
      rewrite /s => + _ {s}; move => -> /=.
      + by move => x /mem_filter /= [neqx0 _]; rewrite /(\o) /idfun /= Sub.val_insubd neqx0.
      by rewrite map_id mem_filter /= rem_filter ?FinType.enum_uniq // mem_filter /predC1.
    rewrite mem_rem_neq // 1?eq_sym // FinType.enumP /=; apply/mapP.
    by exists (Sub.insubd x); rewrite SFT.enumP /= Sub.val_insubd neqx0.
  qed.
end FiniteFieldStruct.


(* ==================================================================== *)
abstract theory SubFiniteZModule.
  type t, st.

  clone import ZModule as ZMod with
    type t <= t.

  clone import SubZModule with
    type t      <= t,
    type st     <= st,
    theory ZMod <- ZMod.

  clone import FiniteZModule as FZMod with
    type t      <= t,
    theory ZMod <- ZMod.

  clone import ZModuleStruct as ZModStr with
    type t      <= t,
    theory ZMod <- ZMod.

  clone import FiniteZModuleStruct as FZModStr with
    type t         <= t,
    theory ZMod    <- ZMod,
    theory ZModStr <- ZModStr,
    theory FZMod   <- FZMod.

  clone include SubFinite with
    type t     <- t,
    type st    <- st,
    op p       <- p,
    theory FT  <- FinType,
    theory Sub <- Sub.

  (*TODO: clone with theory not working here, and neither clone with axiom later..*)
  clone import FiniteZModule as SFZMod with
    type t                  <= st,
    theory ZMod             <- SZMod,
    (*theory FinType          <- SFT.*)
    op FinType.enum         <- senum
    (*axiom FinType.enum_spec <- SFT.enum_spec.*)
    proof *.

  realize FinType.enum_spec by exact SFT.enum_spec.
end SubFiniteZModule.

(* -------------------------------------------------------------------- *)
abstract theory SubFiniteComRing.
  type t, st.

  clone import ComRing as CR with
    type t <= t.

  clone import SubComRing with
    type t    <= t,
    type st   <= st,
    theory CR <- CR.

  clone import FiniteComRing as FCR with
    type t    <= t,
    theory CR <- CR.

  clone import ComRingStruct as CRStr with
    type t    <= t,
    theory CR <- CR.

  clone import FiniteComRingStruct as FCRStr with
    type t       <= t,
    theory CR    <- CR,
    theory CRStr <- CRStr,
    theory FCR   <- FCR.

  clone import SubComRingModule as SCRM with
    type t            <= t,
    type st           <= st,
    theory CR         <- CR,
    theory SubComRing <- SubComRing.

  clone include SubFiniteZModule with
    type t          <- t,
    type st         <- st,
    theory ZMod     <- CR,
    theory FZMod    <- FCR,
    theory ZModStr  <- CRStr,
    theory FZModStr <- FCRStr.

  (*TODO: clone with axiom, or theory.*)
  clone import FiniteComRing as SFCR with
    type t          <= st,
    theory CR       <- SCR,
    (*theory FinType  <- SFZMod.FinType.*)
    op FinType.enum <- senum
    (*axiom FinType.enum_spec <- SFZMod.FinType.enum_spec*)
    proof *.

  realize FinType.enum_spec by exact SFZMod.FinType.enum_spec.

  import ComRingModule.

  op enum_lin (vs : t list) =
    map
      (fun ss => lin ss vs)
      (foldr (allpairs (::)) [[]] (nseq (size vs) senum)).

  lemma enum_lin_nil :
    enum_lin [] = [CR.zeror].
  proof. by rewrite /enum_lin /= nseq0 /= BigZMod.big_nil. qed.

  (*TODO: missing stuff about map and allpairs, in hakyber-eclib?*)
  lemma enum_lin_cons v vs :
    enum_lin (v :: vs) =
    allpairs CR.( + ) (map (transpose SCRM.( ** ) v) senum) (enum_lin vs).
  proof.
    rewrite /enum_lin /= addrC nseqS ?size_ge0 //=; pose el := foldr _ _ _.
    elim: senum el => [|x senum IHsenum] el /=; [by rewrite !allpairs0l|].
    rewrite !allpairs_consl map_cat IHsenum -!map_comp; congr => {IHsenum}.
    by apply/eq_map => xs; rewrite /(\o) /= BigZMod.big_cons /predT /idfun.
  qed.

  lemma enum_linP vs v :
    (v \in enum_lin vs) <=> (gen (vf_oflist vs) v).
  proof.
    elim: vs => [|v' vs IHvs].
    + rewrite enum_lin_nil.
      admit.
    admit.
(*
    rewrite /enum_lin /gen mapP; apply/exists_eq => ss /=.
    rewrite (eq_sym _ v); congr; apply/eq_iff => {v}; split.
    + elim: vs ss => [|v vs IHvs] ss /=; [by rewrite nseq0 /= => ->|].
      rewrite {1}(IntID.addrC 1) nseqS ?size_ge0 //=. allpairsP => -[p].
      by rewrite SFZMod.FinType.enumP /= => -[/IHvs <- ->>].
    elim: vs ss => [|v vs IHvs] ss /=; [by rewrite nseq0 /= size_eq0|].
    case: ss => [|s ss /= /IntID.addrI /IHvs mem_ss {IHvs}] /=.
    + by rewrite addrC -subr_eq eq_sym /= => eq_size; move: (size_ge0 vs); rewrite eq_size.
    rewrite addrC nseqS ?size_ge0 //=; apply/allpairsP; exists (s, ss) => /=.
    by rewrite SFZMod.FinType.enumP.
*)
  qed.

  lemma enum_lin0 :
    enum_lin [] = [CR.zeror].
  proof. by rewrite /enum_lin /= nseq0 /= BigZMod.big_nil. qed.

  lemma size_enum_lin vs :
    size (enum_lin vs) = (size senum) ^ (size vs).
  proof.
    elim: vs => [|v vs IHvs] /=.
    + by rewrite expr0 enum_lin0.
    admit.
  qed.

  lemma free_uniq_enum_lin vs :
    free (vf_oflist vs) =>
    uniq (enum_lin vs).
  proof.
    admit.
  qed.

  lemma gent_enum_lin vs :
    (gen_t (vf_oflist vs)) <=> (forall v , v \in enum_lin vs).
  proof.
    admit.
  qed.

  lemma finite_basis_exists :
    exists vs , basis (vf_oflist vs).
  proof.
    admit.
  qed.

  lemma eq_card_pow :
    exists n , (0 < n) /\ (FCR.FinType.card = SFCR.FinType.card ^ n).
  proof.
    admit.
  qed.
end SubFiniteComRing.

(* -------------------------------------------------------------------- *)
abstract theory SubFiniteIDomain.
  type t, st.

  clone import IDomain as ID with
    type t <= t.

  clone import SubIDomain with
    type t    <= t,
    type st   <= st,
    theory ID <- ID.

  clone import FiniteIDomain as FID with
    type t    <= t,
    theory ID <- ID.

  clone import IDomainStruct as IDStr with
    type t    <= t,
    theory ID <- ID.

  clone import FiniteIDomainStruct as FIDStr with
    type t       <= t,
    theory ID    <- ID,
    theory IDStr <- IDStr,
    theory FID   <- FID.

  clone include SubFiniteComRing with
    type t        <- t,
    type st       <- st,
    theory CR     <- ID,
    theory FCR    <- FID,
    theory CRStr  <- IDStr,
    theory FCRStr <- FIDStr.

  clone import FiniteIDomain as SFID with
    type t          <= st,
    theory ID       <- SID,
    op FinType.enum <- senum
    proof *.

  realize FinType.enum_spec by exact SFCR.FinType.enum_spec.
end SubFiniteIDomain.

(* -------------------------------------------------------------------- *)
abstract theory SubFiniteField.
  type t, st, ut.

  clone import Field as F with
    type t <= t.

  clone import SubField with
    type t   <= t,
    type st  <= st,
    theory F <- F.

  clone import FiniteField as FF with
    type t   <= t,
    theory F <- F.

  clone import FieldStruct as FStr with
    type t   <= t,
    theory F <- F.

  clone import FiniteFieldStruct as FFStr with
    type t      <= t,
    type ut     <= ut,
    theory F    <- F,
    theory FStr <- FStr,
    theory FF   <- FF.

  clone include SubFiniteIDomain with
    type t        <- t,
    type st       <- st,
    theory ID     <- F,
    theory FID    <- FF,
    theory IDStr  <- FStr,
    theory FIDStr <- FFStr.

  clone import FiniteField as SFF with
    type t          <= st,
    theory F        <- SF,
    op FinType.enum <- senum
    proof *.

  realize FinType.enum_spec by exact SFID.FinType.enum_spec.
end SubFiniteField.


(* ==================================================================== *)
abstract theory ZModP_FiniteField.
  type t.

  op p : int.

  axiom prime_p : prime p.

  clone import ZModField as ZModP with
    type zmod     <= t,
    op p          <- p,
    axiom prime_p <- prime_p.

  (*TODO: issue in ZModP: should be a clone with theory ZModP.ZModpField.*)
  clone import Field as F with
    type t          <= t,
    op zeror        <= ZModP.zero,
    op oner         <= ZModP.one,
    op (+)          <= ZModP.(+),
    op [-]          <= ZModP.([-]),
    op ( * )        <= ZModP.( * ),
    op invr         <= ZModP.inv,
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
    type t   <= t,
    theory F <- F.
end ZModP_FiniteField.


(* ==================================================================== *)
abstract theory SubFiniteField_ZMod.
  type t, ut, st.

  clone import Field as F with
    type t <= t.

  clone import FiniteField as FF with
    type t   <= t,
    theory F <- F.

  clone import FieldStruct as FStr with
    type t   <= t,
    theory F <- F.

  clone import FiniteFieldStruct as FFStr with
    type t      <= t,
    type ut     <= ut,
    theory F    <- F,
    theory FStr <- FStr,
    theory FF   <- FF.

  clone import ZModField as ZModP with
    type zmod     <= st,
    op p          <- FStr.char,
    axiom prime_p <- FFStr.prime_char.

(*TODO: the finite import from ZModP_FiniteField is incompatible with the finite from subfinitefield.*)
(*
  clone import ZModP_FiniteField as ZModPFF with
    type t        <= st,
    op p          <- FStr.char,
    axiom prime_p <- FFStr.prime_char,
    theory ZModP  <- ZModP.
*)

  (*TODO: what?*)
(*
  print ofint.
  print F.ofint.
  print ZModPFF.F.ofint.
  print Sub.val.
  print ZModP.Sub.val.
*)

  op is_ofint (x : t) n = (x = F.ofint n).

  op in_zmodP x = exists n , is_ofint x n.

  op insub (x : t) = 
    if in_zmodP x
    then Some (ZModpRing.ofint (argmin idfun (is_ofint x))) 
    else None.

  op val (x : st) = ofint (Sub.val x).

  op wsT = zeror.

  clone import SubField as SF with
    type t       <= t,
    type st      <= st,
    op p         <- in_zmodP,
    op Sub.insub <- insub,
    op Sub.val   <- val,
    op Sub.wsT   <- wsT,
    theory F     <- F
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
    + by rewrite -dvd_char; apply/negP => dvd_; apply/Ndvd/dvdz_mulr.
    rewrite mulrz divrr //.
    + by rewrite -dvd_char; apply/negP => dvd_; apply/Ndvd/dvdz_mulr.
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
    admit.
  qed.

  realize Sub.valP.
  proof. by rewrite /in_zmodP /val; move => x; exists (ZModP.Sub.val x). qed.

  realize Sub.valK.
  proof.
    rewrite /pcancel /insub => x.
    have in_x: (in_zmodP (ofint (ZModP.Sub.val x))).
    + by exists (ZModP.Sub.val x).
    rewrite in_x /=; case: in_x => n is_ofint_.
    move: (argminP idfun (is_ofint (val x)) n _ _).
    + admit.
    + by rewrite /val.
    rewrite /val {1}/is_ofint /idfun /= => ?.
    admit.
  qed.

  realize Sub.insubW.
  proof.
    rewrite /insub /wsT.
    admit.
  qed.

  (*TODO: include.*)
  clone import SubFiniteField as SFF with
    type t       <- t,
    type ut      <- ut,
    type st      <- st,
    theory F     <- F,
    theory FF    <- FF,
    theory FStr  <- FStr,
    theory FFStr <- FFStr.

  lemma eq_char_zmodcard :
    char = SFF.FinType.card.
  proof.
    admit.
  qed.

  lemma eq_card_pow_char :
    exists n , (0 < n) /\ (FF.FinType.card = char ^ n).
  proof.
    rewrite eq_char_zmodcard.
    move: eq_card_pow.
    admit.
  qed.

  op n = ilog char FF.FinType.card.

  lemma lt0n : 0 < n.
  proof.
    admit.
  qed.

  lemma eq_card_char :
    FF.FinType.card = char ^ n.
  proof.
    admit.
  qed.
end SubFiniteField_ZMod.
