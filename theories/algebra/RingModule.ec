(* ==================================================================== *)
require import AllCore List Ring Int SubRing Bigalg StdOrder.
require (*--*) Bigop.
(*---*) import IntOrder.


(* ==================================================================== *)
abstract theory ComRingModule.
  type scalar, t.

  clone import ComRing as CRScalar with
    type t <= scalar.
  clone import ZModule as ZMod with
    type t <= t.

  op ( ** ) : scalar -> t -> t.

  axiom scaleDl (x y : scalar) (a : t) : (x + y) ** a = x ** a + y ** a.
  axiom scaleDr (x : scalar) (a b : t) : x ** (a + b) = x ** a + x ** b.
  axiom scaleM (x y : scalar) (a : t) : (x * y) ** a = x ** (y ** a).
  axiom scale1r (a : t) : oner ** a = a.

  lemma scale0r a :
    CRScalar.zeror ** a = ZMod.zeror.
  proof. by apply/(addrI (CRScalar.zeror ** a)); rewrite -scaleDl !addr0. qed.

  lemma scaler0 (x : scalar) :
    x ** ZMod.zeror = ZMod.zeror.
  proof. by apply/(addrI (x ** ZMod.zeror)); rewrite -scaleDr !addr0. qed.

  lemma scaleN (a : t) :
    (-oner) ** a = -a.
  proof. by rewrite -addr_eq0 addrC -{1}scale1r -scaleDl subrr scale0r. qed.

  lemma scaleNr (x : scalar) (a : t) :
    (-x) ** a = - x ** a.
  proof. by rewrite -mulN1r scaleM scaleN. qed.

  lemma scalerN (x : scalar) (a : t) :
    x ** (-a) = - x ** a.
  proof. by rewrite -addr_eq0 addrC -scaleDr subrr scaler0. qed.

  clone import BigZModule as BigZMod with
    theory ZM <- ZMod.

  clone import BigComRing as BigCR with
    theory CR <- CRScalar.

  lemma scaler_suml ['a] (P : 'a -> bool) (F : 'a -> CRScalar.t) (ss : 'a list) v :
    BigCR.BAdd.big P F ss ** v = BigZMod.big P (fun s => F s ** v) ss.
  proof.
    elim: ss => [|s ss IHss]; [by rewrite BAdd.big_nil BigZMod.big_nil scale0r|].
    by rewrite BAdd.big_cons BigZMod.big_cons; case: (P s) => // _; rewrite scaleDl IHss.
  qed.

  lemma scalel_sumr ['a] (P : 'a -> bool) (F : 'a -> ZMod.t) s (vs : 'a list) :
    s ** BigZMod.big P F vs = BigZMod.big P (fun v => s ** F v) vs.
  proof.
    elim: vs => [|v vs IHvs]; [by rewrite !BigZMod.big_nil scaler0|].
    by rewrite !BigZMod.big_cons; case: (P v) => // _; rewrite scaleDr IHvs.
  qed.

  abbrev lin ss vs : t =
    big predT idfun (map (fun (x : scalar * t) => fst x ** snd x) (zip ss vs)).

  op free p =
    forall ss vs ,
      size ss = size vs =>
      all p vs =>
      uniq vs =>
      lin ss vs = ZMod.zeror =>
      ss = nseq (size vs) CRScalar.zeror.

  op gen p v =
    exists ss vs ,
      size ss = size vs /\
      all p vs /\
      lin ss vs = v.

  op gen_t p =
    forall v ,
      gen p v.

  op basis p =
    (free p) /\ (gen_t p).

  op vf_oflist : t list -> t -> bool = mem.

  op finite_vf p =
    exists vs , forall v , p v <=> vf_oflist vs v.

  (*TODO: this should be /=.*)
  lemma zip_nil1 ['a, 'b] s :
    zip<:'a,'b> [] s = [].
  proof.
    admit.
  qed.

  (*TODO: this should be /=.*)
  lemma zip_nil2 ['a, 'b] s :
    zip<:'a,'b> s [] = [].
  proof.
    admit.
  qed.

  (*TODO: this should be /=.*)
  lemma zip_cons ['a, 'b] (x1 : 'a) (x2 : 'b) (s1 : 'a list) (s2 : 'b list) :
    zip (x1 :: s1) (x2 :: s2) = (x1, x2) :: zip s1 s2.
  proof.
    admit.
  qed.

  lemma lin_nil1 vs :
    lin [] vs = ZMod.zeror.
  proof. by rewrite zip_nil1 big_nil. qed.

  lemma lin_nil2 ss :
    lin ss [] = ZMod.zeror.
  proof. by rewrite zip_nil2 big_nil. qed.

  lemma lin_cons s ss v vs :
    lin (s :: ss) (v :: vs) = (s ** v) + lin ss vs.
  proof. by rewrite zip_cons /= BigZMod.big_cons /predT /idfun. qed.

  lemma lin_cat ss1 ss2 vs1 vs2 :
    size ss1 = size vs1 =>
    lin (ss1 ++ ss2) (vs1 ++ vs2) = lin ss1 vs1 + lin ss2 vs2.
  proof. by move => eq_size; rewrite zip_cat // map_cat BigZMod.big_cat. qed.

  lemma lin0 n vs :
    lin (nseq n CRScalar.zeror) vs = ZMod.zeror.
  proof.
    apply/big1_seq => i [_] /mapP [[s v]] [/mem_zip [+ _]] /=.
    by rewrite mem_nseq => -[_ <<-] ->; rewrite scale0r /idfun.
  qed.

  lemma free_pred0 :
    free pred0.
  proof. by move => ss vs eq_size /all_pred0 /size_eq0 ->> /= _; rewrite nseq0; apply/size_eq0. qed.

  lemma free_gen p v :
    free p => p v => gen p v.
  proof.
    by move => free_p p_v; exists [CRScalar.oner] [v]; rewrite /= p_v /= scale1r big_seq1 /idfun.
  qed.

  lemma free_imp p1 p2 :
    (p1 <= p2)%Core =>
    free p2 =>
    free p1.
  proof.
    move => imp_ free_p1 ss vs eq_size all_p1.
    move: (all_imp_in _ p2 _ _ all_p1); [|by apply/free_p1].
    by apply/allP => ? _ /=; apply/imp_.
  qed.

  lemma genP p v :
    gen p v <=>
    ( exists ss vs ,
        size ss = size vs /\
        all p vs /\
        uniq vs /\
        lin ss vs = v ).
  proof.
    rewrite /gen; split => -[ss vs] [eq_size] [all_p]; [move => eq_v|];
    [|by move => [uniq_vs] eq_v; exists ss vs; do!split].
    exists
      (map
        (fun v => BigCR.BAdd.big (fun (p : scalar * t) => p.`2 = v) fst (zip ss vs))
        (undup vs))
      (undup vs).
    rewrite size_map /= undup_uniq /=; split.
    + by apply/allP => x; rewrite mem_undup => mem_x; move/allP: all_p => ->.
    rewrite zip_mapl_ss !BigZMod.big_mapT.
    rewrite BigZMod.big_mapT BigZMod.big_pairr unzip2_zip in eq_v.
    + by rewrite eq_size.
    rewrite -eq_v => {v eq_v}; apply/BigZMod.eq_big_seq => v.
    rewrite mem_undup => mem_v; rewrite /idfun /(\o) /= scaler_suml.
    rewrite big_filter_cond; apply/congr_big_seq => -[s v'].
    + by move => /mem_zip [mem_s mem_v'] /=; rewrite /predI /predT.
    by move => /mem_zip [mem_s _] /= ->>; rewrite /predI /predT.
  qed.

  lemma free_predU p1 p2 :
    free (predU p1 p2) <=>
    ( (forall v , gen p1 v => gen p2 v => gen (predI p1 p2) v) /\
      free p1 /\
      free p2 ).
  proof.
    split => [free_U|[imp_gen] [free_p1 free_p2]]; [split; [|split]|].
    + move => v /genP [ss1 vs1] [eq_size1] [all_p1] [uniq_vs1 eq_v1].
      move => /genP [ss2 vs2] [eq_size2] [all_p2] [uniq_vs2 eq_v2].
      pose ssvs1C:= filter (predC (p2 \o snd)) (zip ss1 vs1).
      pose ssvs2C:= filter (predC (p1 \o snd)) (zip ss2 vs2).
      pose ssvs1 := filter (p2 \o snd)         (zip ss1 vs1).
      pose ssvs2 := filter (p1 \o snd)         (zip ss2 vs2).
      pose ssvs :=
        map
          (fun p =>
            (fst p - fst (nth (CRScalar.zeror, ZMod.zeror) ssvs2 (find (pred1 (snd p) \o snd) ssvs2)),
             snd p))
          ssvs1.
      exists (map fst ssvs1) (map snd ssvs1).
      rewrite !size_map /=; split.
      - rewrite !all_predI.
        admit.
      move: (free_U ((map fst ssvs1C) ++ (map fst ssvs2C) ++ (map fst ssvs))
                    ((map snd ssvs1C) ++ (map snd ssvs2C) ++ (map snd ssvs))
                    _ _ _ _).
      - by rewrite !size_cat !size_map.
      - admit.
      - admit.
      - admit.
      rewrite !size_cat -!cat_nseq ?addr_ge0 ?size_ge0 // !eqseq_cat.
      - by rewrite !size_cat !size_nseq !ler_maxr ?size_ge0 // !size_map.
      - by rewrite size_nseq ler_maxr ?size_ge0 // !size_map.
      move => [[eq_1C_0 eq_2C_0] eq_0].
      admit.
    + by move: free_U; apply/free_imp => v; apply/(subpredUl p1 p2 v).
    + by move: free_U; apply/free_imp => v; apply/(subpredUr p1 p2 v).
    move => ss vs eq_size all_ uniq_vs eq_0.
    admit.
  qed.

  lemma gen_t_incl p1 p2 :
    (p1 <= p2)%Core =>
    gen_t p1 =>
    gen_t p2.
  proof.
    admit.
  qed.

  lemma gen_cons p1 p2 v :
    gen (predU p1 p2) v <=>
    (exists s1 s2 v1 v2 , gen p1 v1 /\ gen p2 v2 /\ v = s1 ** v1 + s2 ** v2).
  proof.
    admit.
  qed.
end ComRingModule.

(* -------------------------------------------------------------------- *)
abstract theory IDomainModule.
  type scalar, t.

  clone import IDomain as IDScalar with type t <= scalar.

  clone include ComRingModule with
    type scalar     <- scalar,
    type t          <- t,
    theory CRScalar <- IDScalar.
end IDomainModule.

(* -------------------------------------------------------------------- *)
abstract theory VectorSpace.
  type scalar, t.

  clone import Field as FScalar with type t <= scalar.

  clone include IDomainModule with
    type scalar     <- scalar,
    type t          <- t,
    theory IDScalar <- FScalar.
end VectorSpace.


(* ==================================================================== *)
abstract theory SubComRingModule.
  type t, st.

  clone import ComRing as CR with
    type t <= t.

  clone import SubComRing
    with type t <= t,
    type st <= st,
    theory CR <- CR.

  import Sub.

  op ( ** ) (x : st) (a : t) : t =
    val x * a.

  clone ComRingModule with
    type scalar     <- st,
    type t          <- t,
    theory CRScalar <- SubComRing.SCR,
    theory ZMod     <- CR,
    op     ( ** )   <- ( ** )
    proof *.

  realize scaleDl.
  proof. by move=> x y a; rewrite /( ** ) valD mulrDl. qed.

  realize scaleDr.
  proof. by move => x a b; rewrite /( ** ) mulrDr. qed.

  realize scaleM .
  proof. by move => x y a; rewrite /( ** ) valM mulrA. qed.

  realize scale1r.
  proof. by move => a; rewrite /( ** ) val1 mul1r. qed.
end SubComRingModule.

(* -------------------------------------------------------------------- *)
abstract theory SubIDomainModule.
  type t, st.

  clone import IDomain as ID with
    type t <= t.

  clone include SubComRingModule with
    type t    <- t,
    type st   <- st,
    theory CR <- ID.
end SubIDomainModule.

(* -------------------------------------------------------------------- *)
abstract theory SubVectorSpace.
  type t, st.

  clone import Field as F with
    type t <= t.

  clone include SubIDomainModule with
    type t    <- t,
    type st   <- st,
    theory ID <- F.
end SubVectorSpace.
