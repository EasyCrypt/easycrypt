(* ==================================================================== *)
require import AllCore List Ring Int IntDiv RingStruct FinType ZModP Bigalg SubRing RingModule.
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

  clone import UZMod_Field with
    type t   <- t,
    type uz  <- ut,
    theory F <- F.

  clone import SubFinite as SFU with
    type t    <- t,
    type st   <- ut,
    theory FT <- FF.FinType.

  lemma card_unit :
    FF.FinType.card = SFU.SFT.card + 1.
  proof.
    admit.
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

  lemma enum_linP vs v :
    (v \in enum_lin vs) <=> (gen vs v).
  proof.
    admit.
  qed.

  lemma size_enum_lin vs :
    size (enum_lin vs) = (size senum) ^ (size vs).
  proof.
    admit.
  qed.

  lemma free_uniq_enum_lin vs :
    free vs =>
    uniq (enum_lin vs).
  proof.
    admit.
  qed.

  lemma gent_enum_lin vs :
    (gent vs) <=> (forall v , v \in enum_lin vs).
  proof.
    admit.
  qed.

  lemma basis_exists :
    exists vs , basis vs.
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
