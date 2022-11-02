(* ==================================================================== *)
require import AllCore List Ring Int IntMin IntDiv Poly.
require import StdBigop StdPoly Binomial Counting Perms.
(*---*) import StdOrder.IntOrder.


theory SIterOp.

  op siter ['a] (n : int) (f : int -> (int -> 'a) -> 'a) (x : 'a) : 'a =
    (iteri n (fun k m i => if i = k + 1 then f i m else m i) (fun (_ : int) => x)) n.

  lemma siter0 ['a] n f (x : 'a) :
    n <= 0 =>
    siter n f x = x.
  proof. by rewrite /siter => ?; rewrite iteri0. qed.

  lemma siterS ['a] n f (x : 'a) :
    0 <= n =>
    siter (n + 1) f x =
    f (n + 1) (fun k => if (0 <= k <= n) then siter k f x else x).
  proof.
    move => le0n; rewrite /siter; pose g:= (fun k m i => if i = k + 1 then f i m else m i); pose c:= (fun _ => x).
    have iteri_eq: forall i j , iteri i g c j = if (0 <= j <= i) then iteri j g c j else x; last first.
    + by rewrite iteriS // {1}/g /=; congr; apply/fun_ext => k /=; apply/iteri_eq.
    move => i j; case (0 <= i) => [le0i|/ltrNge lti0]; last first.
    + rewrite iteri0 //; [by apply/ltzW|]; rewrite {1}/c /=; case (0 <= j) => //= le0j.
      by rewrite lerNgt (ltr_le_trans _ _ _ lti0 le0j).
    move => {le0n}; elim: i le0i {1 3 4}i  (lerr i) j => [|i le0i IHi] j lej_ k.
    + rewrite iteri0 //; case (0 <= k) => [le0k|/ltrNge ltk0]; rewrite {1}/c //=.
      by case/ler_eqVlt: (ler_trans _ _ _ lej_ le0k) => [<<-/=|]; [rewrite iteri0|move/ltrNge => ->].
    case/ler_eqVlt: lej_ => [->>|/ltzS leji]; [|by apply/IHi].
    case (k = i + 1) => [->>|/ltr_total [/ltzS leki|lt_k]]; [by rewrite addr_ge0| |].
    + by rewrite iteriS // {1}/g ltr_eqF ?ltzS //= IHi // leki /= (ler_trans _ _ _ leki) //; apply/ltzW/ltzS.
    by rewrite iteriS // {1}/g gtr_eqF //= IHi // !(lerNgt k) lt_k /= (ler_lt_trans _ _ _ _ lt_k) //; apply/ltzW/ltzS.
  qed.

end SIterOp.


theory Counting_Argument.

  clone include SIterOp.
  clone import PolyReal.
  clone import Bigint.BIA.
  clone import Bigint.BIM.

  op sPI k m =
    polyXn k -
    PCA.big
     predT
      (fun a =>
        PCM.bigi
          predT
          (fun i =>
            PCM.bigi
              predT
              (fun j => m i + polyC j%r)
              0 (nth 0 a i) *
            polyC (1%r / (fact (nth 0 a i))%r))
          1 (k + 1))
      (rem (shape k (id_perm k)) (allshapes k)).

  op PI (n : int) =
    siter n sPI poly1.

  local lemma lcPI_ n :
    0 <= n =>
    deg (PI n) <= n + 1 /\ (PI n).[n] = if n = 0 then 1%r else 1%r / n%r.
  proof.
    rewrite/PI; elim/sintind: n => n /ler_eqVlt [<<- _|].
    + by rewrite siter0 // deg1 /= polyCE.
    rewrite -(subrK n 1); pose m:= n - 1; move: m => {n} n.
    move/ltzS => le0n IHn; rewrite siterS //= {1}/sPI; split.
    + apply/(ler_trans _ _ _ (degB _ _)); rewrite degXn /= (ler_maxr 0); [by apply/addr_ge0|].
      apply/ler_maxrP => /=; rewrite PCA.big_seq; apply/BigPoly.deg_sum; [by apply/addr_ge0|].
      move=> a; rewrite /= rem_filter.
      - admit.
      move=> /mem_filter; rewrite {1}/predC1 /= => -[neqa /allshapesP /is_shapeP].
      case=> p [is_p_p <<-]; move: neqa; rewrite shape_eq ?is_perm_id //.
      rewrite negb_exists /= => /(_ (id_perm (n + 1))).
      (*TODO: permutations lemmas to simplify this.*)
      rewrite /conj => neq_p_id.
      apply/(ler_trans _ _ _ (BigPoly.deg_prod_le _ _ _ _)).
      - apply/allP => k mem_k; rewrite {1}/predC {1}/predI {1}/predT /=.
        apply/IDPoly.mulf_neq0; [|by rewrite eq_polyC0 RField.unitrV eq_fromint gtr_eqF // fact_gt0].
        apply/prodf_neq0/allP => i mem_i; rewrite /predC /predI /predT /= le2_mem_range.
        move: mem_k; rewrite -(subrK (_ + 2) 1) rangeSr /=; [by apply/subr_ge0|].
        rewrite mem_rcons /=; case=> [->>|mem_k].
        * rewrite mem_range /= -polyCD eq_polyC0 -fromintD eq_fromint gtr_eqF //.
          by rewrite addrC ltzS; move: mem_i; apply/mem_range_le.
        rewrite range_ltn ?ltzS //= mem_k /= poly_eqP negb_forall; exists k.
        rewrite /= negb_imply; split; [by move: mem_k; apply/mem_range_le|].
        rewrite polyDE polyCE poly0E gtr_eqF /=; [by move: mem_k; apply/mem_range_lt|].
        case/(_ k _): IHn; [by apply/mem_range; move: mem_k; apply/mem_range_incl|].
        move=> _ ->; rewrite gtr_eqF /=; [by move: mem_k; apply/mem_range_lt|].
        rewrite -Real.invr0; apply/negP => /RField.invr_inj /=.
        by rewrite eq_fromint gtr_eqF //; move: mem_k; apply/mem_range_lt.
      (*TODO: useless and confusing notation.*)
      print PolyInt.PrePolyInt.IDCoeff.(/).
      apply/ler_subr_addr => /=;
      apply/(ler_trans _ _ _ (Bigint.ler_sum_seq _ _ (fun (i : int) => i * (nth 0 (shape (n + 1) p) i)) _ _)).
      - move=> k mem_k _; rewrite {1}/(\o) /=; apply/(ler_add2r 2) => /=;
        apply/(ler_trans _ _ _ (degM_le _ _ _ _)).
        * apply/prodf_neq0/allP => i mem_i; rewrite /predC /predI /predT /= le2_mem_range.
          move: mem_k; rewrite -(subrK (_ + 2) 1) rangeSr /=; [by apply/subr_ge0|].
          rewrite mem_rcons /=; case=> [->>|mem_k].
          + rewrite mem_range /= -polyCD eq_polyC0 -fromintD eq_fromint gtr_eqF //.
            by rewrite addrC ltzS; move: mem_i; apply/mem_range_le.
          rewrite range_ltn ?ltzS //= mem_k /= poly_eqP negb_forall; exists k.
          rewrite /= negb_imply; split; [by move: mem_k; apply/mem_range_le|].
          rewrite polyDE polyCE poly0E gtr_eqF /=; [by move: mem_k; apply/mem_range_lt|].
          case/(_ k _): IHn; [by apply/mem_range; move: mem_k; apply/mem_range_incl|].
          move=> _ ->; rewrite gtr_eqF /=; [by move: mem_k; apply/mem_range_lt|].
          rewrite -Real.invr0; apply/negP => /RField.invr_inj /=.
          by rewrite eq_fromint gtr_eqF //; move: mem_k; apply/mem_range_lt.
        * rewrite eq_polyC0 -Real.invr0; apply/negP => /RField.invr_inj /=.
          by rewrite eq_fromint gtr_eqF // fact_gt0.
        rewrite degC RField.invr_eq0 eq_fromint gtr_eqF ?fact_gt0 //=.
        apply/ler_subr_addr/(ler_trans _ _ _ (BigPoly.deg_prod_le _ _ _ _)).
        * apply/allP => i mem_i; rewrite /predC /predI /predT /= le2_mem_range.
          move: mem_k; rewrite -(subrK (_ + 2) 1) rangeSr /=; [by apply/subr_ge0|].
          rewrite mem_rcons /=; case=> [->>|mem_k].
          + rewrite mem_range /= -polyCD eq_polyC0 -fromintD eq_fromint gtr_eqF //.
            by rewrite addrC ltzS; move: mem_i; apply/mem_range_le.
          rewrite range_ltn ?ltzS //= mem_k /= poly_eqP negb_forall; exists k.
          rewrite /= negb_imply; split; [by move: mem_k; apply/mem_range_le|].
          rewrite polyDE polyCE poly0E gtr_eqF /=; [by move: mem_k; apply/mem_range_lt|].
          case/(_ k _): IHn; [by apply/mem_range; move: mem_k; apply/mem_range_incl|].
          move=> _ ->; rewrite gtr_eqF /=; [by move: mem_k; apply/mem_range_lt|].
          rewrite -Real.invr0; apply/negP => /RField.invr_inj /=.
          by rewrite eq_fromint gtr_eqF //; move: mem_k; apply/mem_range_lt.
        rewrite /= ler_add2r; apply/(ler_trans _ _ _ (Bigint.ler_sum_seq _ _ (fun _ => k) _ _)).
        * admit.
        rewrite Bigint.bigi_constz //.
        admit.
      admit.
    rewrite gtr_eqF ?ltzS //= {1}/sPI polyDE polyXnE /= addr_ge0 //= polyNE.
    search _ ((PCA.big _ _ _).[_])%PolyReal.
    admit.
  qed.

  op I n q = floor (peval (PI n) q%r).

  lemma le0I n q :
    0 < n =>
    1 < q =>
    0 <= I n q.
  proof.
    admit.
  qed.

  lemma eqI n q :
    0 < n =>
    1 < q =>
    BIA.big
      predT
      (fun a =>
        BIM.bigi
          predT
          (fun d => bin (I d q + nth 0 a d - 1) (nth 0 a d))
          1 (n + 1))
      (allshapes n) =
    q ^ n.
  proof.
    admit.
  qed.

  lemma lt0I n :
    0 < n =>
    exists (q : int) , forall r , q <= r => 0 < I n r.
  proof.
    admit.
  qed.

end Counting_Argument.
