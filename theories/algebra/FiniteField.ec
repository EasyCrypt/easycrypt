require import AllCore List Ring Int IntDiv Characteristic FinType ZModP Bigalg.
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

  clone import FiniteField_Characteristic as FFC with theory FF <- FF.

  clone import BigFiniteField as BigFF with theory FF <- FF.

  op d : int.

  axiom d_spec : exists n , FF.FinType.card = d ^ n.

  op in_subfield x = FF.exp x d = x.

  lemma in_subfield_0 d :
    in_subfield d zeror.
  proof.
    (*by rewrite /in_subfield expr0z => ->.*)
    admit.
  qed.

  lemma in_subfield_1 d :
    in_subfield d oner.
  proof.
    (*by rewrite /in_subfield expr1z.*)
    admit.
  qed.


  qed.

  lemma in_subfield_add d x y : in_subfield d x => in_subfield d y => in_subfield d (x + y).
  proof.
    admit.
  qed.

  lemma in_subfield_mul d x y : in_subfield d x => in_subfield d y => in_subfield d (x * y).
  proof.
    admit.
  qed.

  type sff.

  clone Subtype as Sub with
    type T <- FF.t, type sT <- sff,
    pred P <- in_subfield.

  clone import FiniteField as SFF with
    type t       <- sff,
    op zeror     <- Sub.insubd zeror,
    op (+) x y   <- Sub.insubd (Sub.val x + Sub.val y),
    op ( * ) x y <- Sub.insubd (Sub.val x * Sub.val y)
    proof *.

end SubFiniteField.


abstract theory SubFiniteField.

  clone import FiniteField as FF.

  clone import FiniteField_Characteristic as FFC with theory FF <- FF.

  clone import BigFiniteField as BigFF with theory FF <- FF.

  op d : int.

  axiom d_spec : exists n , FF.FinType.card = d ^ n.

  op in_subfield x = FF.exp x d = x.

  lemma in_subfield_0 d :
    in_subfield d zeror.
  proof.
    (*by rewrite /in_subfield expr0z => ->.*)
    admit.
  qed.

  lemma in_subfield_1 d :
    in_subfield d oner.
  proof.
    (*by rewrite /in_subfield expr1z.*)
    admit.
  qed.


  qed.

  lemma in_subfield_add d x y : in_subfield d x => in_subfield d y => in_subfield d (x + y).
  proof.
    admit.
  qed.

  lemma in_subfield_mul d x y : in_subfield d x => in_subfield d y => in_subfield d (x * y).
  proof.
    admit.
  qed.

  type sff.

  clone Subtype as Sub with
    type T <- FF.t, type sT <- sff,
    pred P <- in_subfield.

  clone import FiniteField as SFF with
    type t       <- sff,
    op zeror     <- Sub.insubd zeror,
    op (+) x y   <- Sub.insubd (Sub.val x + Sub.val y),
    op ( * ) x y <- Sub.insubd (Sub.val x * Sub.val y)
    proof *.

  realize addrA.
  proof.
    move => x y z.
    search _ Sub.insubd Sub.val.
  qed.

  realize addrC.
  proof.
    admit.
  qed.

  realize addr0r.
  proof.
    admit.
  qed.

  realize addrNr.
  proof.
    admit.
  qed.

  realize oner_neq0.
  proof.
    admit.
  qed.

  realize mulrA.
  proof.
    admit.
  qed.

  realize mulrC.
  proof.
    admit.
  qed.

  realize mul1r.
  proof.
    admit.
  qed.

  realize mulrDl.
  proof.
    admit.
  qed.

  realize mulVr.
  proof.
    admit.
  qed.

  realize unitP.
  proof.
    admit.
  qed.

  realize unitout.
  proof.
    admit.
  qed.

  realize mulf_eq0.
  proof.
    admit.
  qed.

  realize FinType.enum_spec.
  proof.
    admit.
  qed.

(*
  lemma in_subfield_imp x (d n : int) :
    (exists (k : int) , k <> 0 /\ n = d ^ k) =>
    in_subfield d x =>
    in_subfield n x.
  proof.
    move => [k] [neqk0 ->>]; rewrite /in_subfield.
    (*TODO: hakyber-eclib*)
    print pow_normr.
    have ->: forall (d k : int), d ^ k = d ^ `|k| by admit.
    move/normr_gt0: neqk0; move: `|k| => {k} k lt0k.
    move/subr_eq0 => eq_; apply/subr_eq0.
    


    rewrite ltzE /= -(IntID.subrK k 1) ler_addr.
    move: (k - 1) => {k}; elim => [|k le0k IHk] x; [by rewrite IntID.expr1|].
    rewrite -(IntID.subrK k (-1)) opprK in le0k.
    move: (k + 1) le0k IHk => {k} k; rewrite ler_subr_addl /= => le1k IHk.
    
  qed.

  lemma in_subfield_card x :
    in_subfield card x.
  proof.
    search _ card.
    search _ Finite.to_seq.
    search _ enum.
    rewrite /card; move: enum_uniq enumP.
    admit.
  qed.
*)

end SubFiniteField.


abstract theory ZModP_SubFiniteField.

  clone import ZModField as Fp with
    op p <- char,
    axiom prime_p <- prime_char.

  op ofzmod (x : zmod) = ofint (Fp.Sub.val x).

end ZModP_SubFIniteField.


abstract theory ZModField_Finite.

  clone include FiniteField.

  (*TODO*)
  (*clone include ZModField.*)

end ZModField_Finite.
