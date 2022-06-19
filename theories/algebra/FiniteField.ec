require import AllCore List Ring Int IntDiv Characteristic FinType ZModP Bigalg SubRing.
require (*--*) Subtype.
(*---*) import StdOrder.IntOrder.


abstract theory FiniteField.

  clone include Field.

  clone import FinType.FinType as FinType with type t <= t.

end FiniteField.


abstract theory FiniteField_Characteristic.

  clone import FiniteField as FF.

  clone include Field_Characteristic with theory F <- FF.

  lemma prime_char : prime char.
  proof.
    case: char_integral => // /char0P inj_ofint; have //: false.
    move: (uniq_map_injective _ (range 0 (size FinType.enum + 1)) inj_ofint).
    rewrite range_uniq /=; apply/negP => uniq_; move: (uniq_leq_size _ FF.FinType.enum uniq_).
    rewrite size_map size_range ler_maxr /=; [by apply/addr_ge0 => //; apply/size_ge0|].
    by rewrite ger_addl /= => ? _; apply/FinType.enumP.
  qed.

end FiniteField_Characteristic.


abstract theory BigFiniteField.

   clone import FiniteField as FF.

   clone import BigComRing as BigFF with theory CR <- FF.

   lemma geo_sum n x :
     0 <= n =>
     (oner - FF.exp x n) = (oner - x) * (BAdd.bigi predT (FF.exp x) 0 n).
   proof.
     move => le0n; rewrite mulrDl mul1r mulNr BAdd.mulr_sumr.
     rewrite (BAdd.eq_big_int _ _ (fun (i : int) => x * exp x i) ((exp x) \o ((+) 1))).
     + by move => i [? _]; rewrite /(\o) /= addrC exprS.
     rewrite -BAdd.big_mapT -range_add /=; case/ler_eqVlt: le0n => [<<-|lt0n].
     + by rewrite !range_geq // BAdd.big_nil expr0 !subrr.
     rewrite /= range_ltn // BAdd.big_consT expr0 rangeSr -?ltzS -?ltr_subl_addr //.
     by rewrite BAdd.big_rcons /predT /= (addrC (BAdd.big _ _ _)) subr_add2r.
   qed.

end BigFiniteField.


abstract theory SubFiniteField.

  clone import FiniteField as FF.

  clone include SubField with
    theory F <- FF.

  op senum = (map Sub.insubd (filter in_sub FF.FinType.enum)).

  clone import FiniteField as SFF with
    type t          <- st,
    op zeror        <- zeror,
    op (+)          <- (+),
    op [-]          <- ([-]),
    op oner         <- oner,
    op ( * )        <- ( * ),
    op invr         <- invr,
    op FinType.enum <- senum
    proof *.

  realize addrA     by exact SF.addrA.
  realize addrC     by exact SF.addrC.
  realize add0r     by exact SF.add0r.
  realize addNr     by exact SF.addNr.
  realize oner_neq0 by exact SF.oner_neq0.
  realize mulrA     by exact SF.mulrA.
  realize mulrC     by exact SF.mulrC.
  realize mul1r     by exact SF.mul1r.
  realize mulrDl    by exact SF.mulrDl.
  realize mulVr     by exact SF.mulVr.
  realize unitP     by exact SF.unitP.
  realize unitout   by exact SF.unitout.
  realize mulf_eq0  by exact SF.mulf_eq0.

  realize FinType.enum_spec.
  proof.
    move => x; rewrite /senum count_map count_filter /predI /preim.
    rewrite -(FF.FinType.enum_spec (Sub.val x)); apply/eq_count.
    move => y; rewrite /pred1 /=; split => [[<<- in_sub_y]|->>].
    + by rewrite Sub.val_insubd in_sub_y.
    by rewrite Sub.valKd /= Sub.valP.
  qed.

  clone import FiniteField_Characteristic as FFC with theory FF <- FF.

  clone import BigFiniteField as BigFF with theory FF <- FF.

  lemma sub_card :
    exists d , 0 < d /\ FF.FinType.card = SFF.FinType.card ^ d.
  proof.
    admit.
  qed.

end SubFiniteField.


abstract theory SubFiniteField_Card.

  clone import FiniteField as FF.

  op scard : int.

  axiom scard_spec : exists d , FF.FinType.card = scard ^ d.

  op in_sub x = FF.exp x scard = x.

  clone import SubFiniteField with
    theory FF <- FF,
    op w      <- FF.zeror,
    op wu     <- FF.oner
  proof sub_w, sub_add, sub_opp, unit_wu, sub_wu, sub_mul, sub_inv.

  realize sub_w.
  proof.
    admit.
  qed.

  realize sub_add.
  proof.
    admit.
  qed.

  realize sub_opp.
  proof.
    admit.
  qed.

  realize unit_wu.
  proof.
    admit.
  qed.

  realize sub_wu.
  proof.
    admit.
  qed.

  realize sub_mul.
  proof.
    admit.
  qed.

  realize sub_inv.
  proof.
    admit.
  qed.

end SubFiniteField_Card.


abstract theory ZModP_SubFiniteField.

  clone import FiniteField as FF.

  clone import FiniteField_Characteristic as FFC with theory FF <- FF.

  clone import ZModField as Fp with
    op p          <- FFC.char,
    axiom prime_p <- FFC.prime_char.

  op ofzmod (x : zmod) = ofint (Fp.Sub.val x).

end ZModP_SubFiniteField.


abstract theory ZModField_Finite.

  clone include FiniteField.

  (*TODO*)
  (*clone include ZModField.*)

end ZModField_Finite.
