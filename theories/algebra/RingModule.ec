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

  lemma scale_unit (x : scalar) (a : t) :
    unit x =>
    x ** a = ZMod.zeror =>
    a = ZMod.zeror.
  proof. by move => /unitrP [y] eq1 eq0; rewrite -scale1r -eq1 scaleM eq0 scaler0. qed.

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

  op gen p v =
    exists ss vs ,
      size ss = size vs /\
      all p vs /\
      lin ss vs = v.

  op gen_t p =
    forall v ,
      gen p v.

  op free p =
    forall ss vs ,
      size ss = size vs =>
      all p vs =>
      uniq vs =>
      lin ss vs = ZMod.zeror =>
      ss = nseq (size vs) CRScalar.zeror.

  op basis p =
    (free p) /\ (gen_t p).

  op vf_oflist : t list -> t -> bool = mem.

  op finite_vf p =
    exists vs , forall v , p v <=> vf_oflist vs v.

  lemma lin_nil1 vs :
    lin [] vs = ZMod.zeror.
  proof. by rewrite zip_nil1 big_nil. qed.

  lemma lin_nil2 ss :
    lin ss [] = ZMod.zeror.
  proof. by rewrite zip_nil2 big_nil. qed.

  lemma lin_cons s ss v vs :
    lin (s :: ss) (v :: vs) = (s ** v) + lin ss vs.
  proof. by rewrite /= BigZMod.big_cons /predT /idfun. qed.

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

  lemma lin_scaleM s ss vs :
    s ** lin ss vs = lin (map (( * ) s) ss) vs.
  proof.
    rewrite scalel_sumr zip_mapl !BigZMod.big_mapT.
    apply/BigZMod.eq_big_seq => -[s' v] /mem_zip [mem_s' mem_v].
    by rewrite /idfun /(\o) /= scaleM.
  qed.

  lemma lin_split p ss vs :
    exists ss1 ss2 vs1 vs2 ,
      size ss1 = size vs1 /\
      size ss2 = size vs2 /\
      perm_eq (zip ss vs) (zip ss1 vs1 ++ zip ss2 vs2) /\
      all p vs1         /\
      all (predC p) vs2 /\
      lin ss vs = lin ss1 vs1 + lin ss2 vs2.
  proof.
    exists (unzip1 (filter (p \o snd)         (zip ss vs)))
           (unzip1 (filter (predC (p \o snd)) (zip ss vs)))
           (unzip2 (filter (p \o snd)         (zip ss vs)))
           (unzip2 (filter (predC (p \o snd)) (zip ss vs))).
    do!split.
    + by rewrite !size_map.
    + by rewrite !size_map.
    + by rewrite !zip_unzip perm_eq_sym perm_filterC.
    + rewrite all_map; apply/all_filterP; rewrite -filter_predI; apply/eq_in_filter => -[s v].
      by move => /mem_zip [mem_s mem_v]; rewrite /predI /preim /(\o).
    + rewrite all_map; apply/all_filterP; rewrite -filter_predI; apply/eq_in_filter => -[s v].
      by move => /mem_zip [mem_s mem_v]; rewrite /predI /predC /preim /(\o).
    rewrite !zip_unzip !big_mapT -big_cat.
    by apply/eq_big_perm/perm_eq_sym/perm_filterC.
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

  lemma gen0 p :
    gen p ZMod.zeror.
  proof. by exists [] []; rewrite lin_nil1. qed.

  lemma gen_pred0 v :
    gen pred0 v <=>
    v = ZMod.zeror.
  proof.
    split => [[ss vs] |>|->>]; [|by apply/gen0].
    by rewrite all_pred0 size_eq0 => + ->> /=; rewrite lin_nil2.
  qed.

  lemma gen_predT v :
    gen predT v.
  proof. by exists [oner] [v]; rewrite lin_cons lin_nil1 scale1r addr0 /predT. qed.

  lemma gen_pred1 v w :
    gen (pred1 v) w <=> (exists s , w = s ** v).
  proof.
    split => [[ss vs] |> eq_size /all_pred1P eq_|[s] ->>]; last first.
    + by exists [s] [v]; rewrite lin_cons lin_nil1 /pred1 addr0.
    move: eq_size eq_ => <- ->>; exists (BigCR.BAdd.big predT idfun ss).
    elim: ss => [|s ss IHss].
    + by rewrite lin_nil1 BigCR.BAdd.big_nil scale0r.
    rewrite /= addrC nseqS ?size_ge0 // lin_cons BigCR.BAdd.big_cons.
    by rewrite IHss -scaleDl /predT /idfun.
  qed.

  lemma gen_lin p ss vs :
    all p vs =>
    gen p (lin ss vs).
  proof.
    move => all_; exists (unzip1 (zip ss vs)) (unzip2 (zip ss vs)) => /=.
    rewrite !size_map zip_unzip /= zip_take unzip2_zip.
    + rewrite !size_take.
      - by rewrite /min; case (_ < _)%Int => /=; rewrite size_ge0.
      - by rewrite /min; case (_ < _)%Int => /=; rewrite size_ge0.
      rewrite /min; case: (size ss < size vs) => [->|] //=.
      by case/lerNgt/ler_eqVlt => ->.
    by apply/allP => x /mem_take; move/allP: all_ => all_; apply/all_.
  qed.

  lemma gen_add p v1 v2 :
    gen p v1 =>
    gen p v2 =>
    gen p (v1 + v2).
  proof.
    move => [ss1 vs1] [? [? ?]] [ss2 vs2] [? [? ?]].
    exists (ss1 ++ ss2) (vs1 ++ vs2); do!split.
    + by rewrite !size_cat; congr.
    + by apply/all_cat.
    by rewrite lin_cat //; congr.
  qed.

  lemma gen_scale p s v :
    gen p v =>
    gen p (s ** v).
  proof.
    move => [ss vs] [? [? ?]]; exists (map (( * ) s) ss) vs.
    by rewrite size_map /=; do!split => //; rewrite -lin_scaleM; congr.
  qed.

  lemma gen_scale_unit p s v :
    unit s =>
    gen p v <=>
    gen p (s ** v).
  proof.
    move => /unitrP [y] eq1; split; [by apply/gen_scale|].
    by move => /(gen_scale _ y); rewrite -scaleM eq1 scale1r.
  qed.

  lemma gen_opp p v :
    gen p v =>
    gen p (-v).
  proof. by move => /(gen_scale _ (-CRScalar.oner) _); rewrite scaleN. qed.

  lemma gen_p p v :
    p v =>
    gen p v.
  proof. by move => pv; exists [CRScalar.oner] [v]; rewrite lin_cons lin_nil1 scale1r addr0. qed.

  lemma gen_imp p1 p2 v :
    (p1 <= p2)%Core =>
    gen p1 v =>
    gen p2 v.
  proof.
    move => imp_ -[ss vs] [? [all_ ?]].
    exists ss vs; do!split => //; move: all_; apply/all_imp_in/allP.
    by move => ? _ /=; apply/imp_.
  qed.

  lemma gen_eq p1 p2 v :
    (forall x , p1 x <=> p2 x) =>
    gen p1 v <=> gen p2 v.
  proof. by move => eq_ ; split; apply/gen_imp => ? /eq_. qed.

  lemma gen_predI1 p1 p2 v :
    gen (predI p1 p2) v =>
    gen p1 v.
  proof. by apply/gen_imp => ?; rewrite /predI. qed.

  lemma gen_predI2 p1 p2 v :
    gen (predI p1 p2) v =>
    gen p2 v.
  proof. by apply/gen_imp => ?; rewrite /predI. qed.

  lemma gen_predU p1 p2 v :
    gen (predU p1 p2) v <=>
    (exists s1 s2 v1 v2 , gen p1 v1 /\ gen p2 v2 /\ v = s1 ** v1 + s2 ** v2).
  proof.
    split => [[ss vs] [eq_size [all_ eq_v]]|]; last first.
    + move => [s1 s2 v1 v2] [] [ss1 vs1] [eq_size1 [all_1 <<-]].
      move => [] [ss2 vs2] [eq_size2 [all_2 <<-]] ->>.
      rewrite !lin_scaleM -lin_cat ?size_map //; apply/gen_lin.
      by rewrite all_cat; split; [apply/all_predU1|apply/all_predU2].
    pose ssvs  := filter (p1 \o snd)         (zip ss vs).
    pose ssvsC := filter (predC (p1 \o snd)) (zip ss vs).
    exists CRScalar.oner CRScalar.oner
           (lin (map fst ssvs) (map snd ssvs)) (lin (map fst ssvsC) (map snd ssvsC)).
    rewrite !scale1r -eq_v => {v eq_v}; split; [|split].
    + apply/gen_lin; rewrite all_map.
      by rewrite /ssvs /(\o) /preim /= filter_all.
    + apply/gen_lin; rewrite all_map.
      apply/all_filterP; rewrite -filter_predI; apply/eq_in_filter => -[s v].
      move => /mem_zip [mem_s mem_v]; move/allP/(_ _ mem_v): all_.
      by rewrite /predI /predU /predC /preim /(\o) /=; case: (p1 v).
    rewrite -lin_cat ?size_map // zip_cat ?size_map // !zip_unzip.
    by apply/eq_big_perm/perm_eq_map/perm_eq_sym/perm_filterC.
  qed.

  lemma gen_split p2 p1 v :
    gen p1 v <=>
    ( exists s1 s2 v1 v2 ,
        gen (predI p1 p2)         v1 /\
        gen (predI p1 (predC p2)) v2 /\
        v = s1 ** v1 + s2 ** v2).
  proof.
    rewrite -gen_predU; apply/gen_eq => ?; rewrite /predU /predI /predC /=.
    by case: (p1 _); case: (p2 _).
  qed.

  lemma gen_t_pred0 :
    gen_t pred0 <=> (forall v , v = ZMod.zeror).
  proof. by apply/forall_eq => ? /=; rewrite gen_pred0. qed.

  lemma gen_t_predT :
    gen_t predT.
  proof. by move => ?; apply/gen_predT. qed.

  lemma gen_t_pred1 v :
    gen_t (pred1 v) <=> (forall w , exists s , w = s ** v).
  proof. by apply/forall_eq => x /=; apply/eqboolP/gen_pred1. qed.

  lemma gen_t_imp p1 p2 :
    (p1 <= p2)%Core =>
    gen_t p1 =>
    gen_t p2.
  proof.
    move => imp_ gen_t1 v; move: gen_t1 => /(_ v) [ss vs] |> ? all_.
    exists ss vs; do!split => //; move: all_; apply/all_imp_in/allP.
    by move => ? _ /=; apply/imp_.
  qed.

  lemma gen_t_eq p1 p2 :
    (forall x , p1 x <=> p2 x) =>
    gen_t p1 <=> gen_t p2.
  proof. by move => eq_ ; apply/forall_eq => v /=; apply/eqboolP/gen_eq. qed.

  lemma gen_t_predI1 p1 p2 :
    gen_t (predI p1 p2) =>
    gen_t p1.
  proof. by apply/gen_t_imp => ?; rewrite /predI. qed.

  lemma gen_t_predI2 p1 p2 :
    gen_t (predI p1 p2) =>
    gen_t p2.
  proof. by apply/gen_t_imp => ?; rewrite /predI. qed.

  lemma gen_t_predU p1 p2 :
    gen_t (predU p1 p2) <=>
    (forall v , exists s1 s2 v1 v2 , gen p1 v1 /\ gen p2 v2 /\ v = s1 ** v1 + s2 ** v2).
  proof. by apply/forall_eq => v /=; apply/eqboolP/gen_predU. qed.

  lemma gen_t_split p2 p1 :
    gen_t p1 <=>
    ( forall v , exists s1 s2 v1 v2 ,
        gen (predI p1 p2)         v1 /\
        gen (predI p1 (predC p2)) v2 /\
        v = s1 ** v1 + s2 ** v2).
  proof. by apply/forall_eq => v /=; apply/eqboolP/gen_split. qed.

  lemma free0 p :
    free p =>
    ! p ZMod.zeror.
  proof.
    move => /(_ [CRScalar.oner] [ZMod.zeror]); rewrite lin_cons lin_nil1 /=.
    by rewrite scale1r addr0 nseq1 /= oner_neq0.
  qed.

  lemma free_pred0 :
    free pred0.
  proof. by move => ss vs eq_size /all_pred0 /size_eq0 ->> /= _; rewrite nseq0; apply/size_eq0. qed.

  lemma free_predT :
    ! free predT.
  proof. by apply/negP => /free0. qed.

  lemma free_pred1 v :
    free (pred1 v) <=> (forall s , s ** v = ZMod.zeror => s = CRScalar.zeror).
  proof.
    split => [free1 s eq0|free1 ss vs eq_size /all_pred1P].
    + by move/(_ [s] [v] _ _ _ _): free1; rewrite ?lin_cons ?lin_nil1 ?addr0 ?nseq1.
    move: eq_size => <- ->>; move/ler_eqVlt: (size_ge0 ss) => [eq_size|].
    + by rewrite -eq_size !nseq0 -size_eq0 eq_size.
    move/ltzE/ler_eqVlt => /= [eq_size|/ltzE /subr_ge0 le2size].
    + rewrite -eq_size !nseq1; case/eq_sym/size_eq1: eq_size => x ->> _.
      by rewrite lin_cons lin_nil1 addr0 => /free1.
    rewrite -(IntID.subrK (size ss) (1 + 1)); move: (size ss - (1 + 1)) le2size => n le0n.
    by rewrite addrA !nseqS ?addr_ge0.
  qed.

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

  lemma free_eq p1 p2 :
    (forall x , p1 x <=> p2 x) =>
    free p1 <=> free p2.
  proof. by move => eq_ ; split; apply/free_imp => ? /eq_. qed.

  lemma free_predI1 p1 p2 :
    free p1 =>
    free (predI p1 p2).
  proof. by apply/free_imp => ?; rewrite /predI. qed.

  lemma free_predI2 p1 p2 :
    free p2 =>
    free (predI p1 p2).
  proof. by apply/free_imp => ?; rewrite /predI. qed.

  lemma free_predU p1 p2 :
    free (predU p1 p2) <=>
    ( (forall v , gen p1 v => gen p2 v => gen (predI p1 p2) v) /\
      free p1 /\
      free p2 ).
  proof.
    split => [free_U|[imp_gen] [free_p1 free_p2]]; [split; [|split]|].
    + move => v /(gen_split p2) [s11 s21 v11 v21] [gen1 [gen1C eq_v1]].
      move =>   /(gen_split p1) [s12 s22 v12 v22] [gen2 [gen2C eq_v2]].
      rewrite (gen_eq _ (predI p1 p2)) in gen2; [by move => ?; rewrite predIC|].
      move/(gen_scale _ s11): gen1  => gen1;  move/(gen_scale _ s12)/gen_opp: gen2  => gen2.
      move/(gen_scale _ s21): gen1C => gen1C; move/(gen_scale _ s22)/gen_opp: gen2C => gen2C.
      move: (gen_add _ _ _ gen1 gen2) gen1C gen2C => {gen2}.
      move => /genP [ss vs]   [size_eq  [all_  [uniq_  eq_lin]]].
      move => /genP [ss1 vs1] [size_eq1 [all_1 [uniq_1 eq_lin1]]].
      move => /genP [ss2 vs2] [size_eq2 [all_2 [uniq_2 eq_lin2]]].
      move/(_ (ss ++ ss1 ++ ss2) (vs ++ vs1 ++ vs2) _ _ _ _): free_U.
      - by rewrite !size_cat size_eq size_eq1 size_eq2.
      - by rewrite !all_cat; do!split; [move: all_|move: all_1|move: all_2];
        apply/all_imp_in/allP => x mem_x; rewrite /predI /predU /predC /=;
        case: (p1 x).
      - rewrite !cat_uniq uniq_ uniq_1 uniq_2 /=; split.
        * apply/negP => /hasP [?] [mem_1 mem_]; move/allP/(_ _ mem_): all_.
          by move/allP/(_ _ mem_1): all_1; rewrite /predI /predC => -[-> ->].
        apply/negP => /hasP [?] [mem_2 /mem_cat mem_or]; move/allP/(_ _ mem_2): all_2.
        by case: mem_or => [mem_|mem_1]; [move/allP/(_ _ mem_): all_|move/allP/(_ _ mem_1): all_1];
        rewrite /predI /predC => -[-> ->].
      - rewrite !lin_cat ?size_cat ?size_eq ?size_eq1 // eq_lin eq_lin1 eq_lin2.
        by rewrite (addrAC (s11 ** v11)) -eq_v1 -addrA -opprD -eq_v2 subrr.
      rewrite !size_cat -!cat_nseq ?addr_ge0 ?size_ge0 // !eqseq_cat.
      - by rewrite !size_cat !size_nseq !ler_maxr ?size_ge0 // size_eq size_eq1.
      - by rewrite size_nseq ler_maxr // size_ge0.
      move => [[->> ->>] ->>] {size_eq size_eq1 size_eq2 eq_lin eq_lin2 eq_v2}.
      by move: eq_lin1 eq_v1; rewrite lin0 => <- ->; rewrite addr0.
    + by move: free_U; apply/free_imp => v; apply/(subpredUl p1 p2 v).
    + by move: free_U; apply/free_imp => v; apply/(subpredUr p1 p2 v).
    move => ss vs eq_size all_ uniq_; case: (lin_split p1 ss vs).
    move => ss1 ss2 vs1 vs2 |> eq_size1 eq_size2 perm_eq_ all_1 all_2 -> /addr_eq0.
    move: (perm_eq_); rewrite -zip_cat // => /(perm_eq_map snd).
    rewrite !unzip2_zip ?size_cat ?eq_size ?eq_size1 ?eq_size2 // => perm_eq_vs.
    move: (perm_eq_vs) => /perm_eq_mem eq_mem.
    move: (all_predI (predU p1 p2) (predC p1) vs2); rewrite all_2 /= => -[_] /(_ _).
    + by apply/allP => x mem_x; move/allP/(_ x): all_ => -> //; rewrite eq_mem mem_cat mem_x.
    move => all_2'; move: (all_imp_in _ p2 _ _ all_2') => /=.
    + by apply/allP => x mem_x; rewrite /predI /predU /predC /=; case: (p1 x).
    move => {all_2'} all_2'; rewrite -scaleN lin_scaleM => eq_lin; move: (imp_gen (lin ss1 vs1) _ _).
    + by apply/gen_lin.
    + rewrite eq_lin; apply/gen_lin; move: (all_predI (predU p1 p2) (predC p1) vs2).
      rewrite all_2 /= => -[_] /(_ _).
      - by apply/allP => x mem_x; move/allP/(_ x): all_ => -> //; rewrite eq_mem mem_cat mem_x.
      by apply/all_imp_in/allP => x mem_x; rewrite /predI /predU /predC /=; case: (p1 x).
    move => /genP [ss0 vs0] |> eq_size0 all_0 uniq_0 eq_lin0; move: (eq_lin); rewrite -eq_lin0.
    rewrite -lin_scaleM scaleN -addr_eq0 -lin_cat // => eq_lin2; move: (free_p2 _ _ _ _ _ eq_lin2).
    + by rewrite !size_cat eq_size0 eq_size2.
    + rewrite all_cat; split => //; move: all_0.
      by apply/all_imp_in/allP => x mem_x; rewrite /predI /predU /predC /=; case: (p1 x).
    + rewrite cat_uniq uniq_0 /=; split.
      - apply/negP => /hasP [x] [mem_x2 mem_x0]; move: all_2 all_0.
        move => /allP /(_ _ mem_x2) + /allP /(_ _ mem_x0).
        by rewrite /predI /predC /=; case: (p1 x).
      by move: (perm_eq_uniq _ _ perm_eq_vs); rewrite uniq_ /= cat_uniq.
    rewrite size_cat -cat_nseq ?size_ge0 // eqseq_cat ?size_nseq ?ler_maxr ?size_ge0 //.
    move => [->> ->>]; move: {eq_size0 eq_size2 eq_lin eq_lin2} eq_lin0.
    rewrite lin0 eq_sym => eq_lin; move: (free_p1 _ _ _ _ _ eq_lin) => //.
    + by move: (perm_eq_uniq _ _ perm_eq_vs); rewrite uniq_ /= cat_uniq.
    move => ->>; move: perm_eq_; rewrite -zip_cat ?size_nseq ?ler_maxr ?size_ge0 //.
    move => /(perm_eq_map fst).
    rewrite !unzip1_zip ?size_cat ?size_nseq ?eq_size ?ler_maxr ?size_ge0 //.
    rewrite cat_nseq ?size_ge0 //; move/perm_eq_size: perm_eq_vs; rewrite size_cat => <-.
    by move => /(perm_eq_nseq predT).
  qed.

  lemma free_split p1 p2 :
    free p1 <=>
    ( (forall v , gen (predI p1 p2) v => gen (predI p1 (predC p2)) v => v = ZMod.zeror) /\
      free (predI p1 p2) /\
      free (predI p1 (predC p2)) ).
  proof.
    rewrite (free_eq _ (predU (predI p1 p2) (predI p1 (predC p2)))).
    + by move => x; rewrite /predU /predI /predC; case: (p1 x); case: (p2 x).
    rewrite free_predU; apply/eqboolP; congr; apply/eqboolP/forall_eq => x /=.
    case: (gen _ _) => //=; case: (gen _ _) => //=; apply/eqboolP.
    by rewrite (gen_eq _ pred0) ?gen_pred0 // => y; rewrite /predI /predC /pred0; case: (p2 y).
  qed.

  lemma free_predU1 p v :
    free (predU (pred1 v) p) <=>
    ( (p v \/ (forall s , gen p (s ** v) => s = CRScalar.zeror)) /\
      free p).
  proof.
    rewrite free_predU; split => [|> imp_gen /free_pred1 imp_eq0 free_|].
    + case: (p v) => [|Npv /= s gen_] //.
      move: (imp_gen _ _ gen_); [by apply/gen_pred1; exists s|].
      rewrite (gen_eq _ pred0) ?gen_pred0 => [|/imp_eq0 //].
      by move => x; rewrite /predI /pred1 /pred0 /=; case (x = v) => [->>|].
    move => |> [pv|imp_eq0] free_; split.
    + move => ? /gen_pred1 [s] ->> _; rewrite (gen_eq _ (pred1 v)) ?gen_scale ?gen_p //=.
      by move => x; rewrite /predI /pred1; case (x = v) => [->>|].
    + by move: free_; apply/free_imp => ? ->.
    + by move => ? /gen_pred1 [s] ->> /imp_eq0 ->>; rewrite scale0r gen0.
    by apply/free_pred1 => s eq0; apply/imp_eq0; rewrite eq0 gen0.
  qed.

  lemma vf_oflist_nil v :
    ! vf_oflist [] v.
  proof. by trivial. qed.

  lemma vf_oflist_cons v vs :
    forall w , vf_oflist (v :: vs) w <=> (predU (pred1 v) (vf_oflist vs)) w.
  proof. by rewrite /predU /pred1 /vf_oflist. qed.

  lemma gen_vf_oflist_nil v :
    gen (vf_oflist []) v <=> (v = ZMod.zeror).
  proof. by rewrite (gen_eq _ pred0) ?gen_pred0. qed.

  lemma gen_vf_oflist_cons v vs w :
    gen (vf_oflist (v :: vs)) w <=>
    (exists s1 s2 w2 , gen (vf_oflist vs) w2 /\ w = s1 ** v + s2 ** w2).
  proof.
    rewrite (gen_eq _ (predU (pred1 v) (vf_oflist vs)) _ (vf_oflist_cons v vs)).
    rewrite gen_predU; split => [[s1 s2 v1 v2]|[s1 s2 w2]] |>.
    + move => /gen_pred1 [s] ->> gen_v2; exists (s1 * s) s2 v2.
      by rewrite gen_v2 scaleM.
    by move => gen_w2; exists s1 s2 v w2; rewrite gen_w2 /= gen_p.
  qed.

  lemma gen_t_vf_oflist_nil :
    gen_t (vf_oflist []) <=> (forall v , v = ZMod.zeror).
  proof. by rewrite (gen_t_eq _ pred0) ?gen_t_pred0. qed.

  lemma gen_t_vf_oflist_cons v vs :
    gen_t (vf_oflist (v :: vs)) <=>
    (forall w , exists s1 s2 w2 , gen (vf_oflist vs) w2 /\ w = s1 ** v + s2 ** w2).
  proof. by apply/forall_eq => x /=; apply/eqboolP/gen_vf_oflist_cons. qed.

  lemma free_vf_oflist_nil :
    free (vf_oflist []).
  proof. by rewrite (free_eq _ pred0) ?free_pred0. qed.

  lemma free_vf_oflist_cons v vs :
    free (vf_oflist (v :: vs)) <=>
    ( (v \in vs \/ (forall s , gen (vf_oflist vs) (s ** v) => s = CRScalar.zeror)) /\
      free (vf_oflist vs)).
  proof.
    rewrite (free_eq _ (predU (pred1 v) (vf_oflist vs)) (vf_oflist_cons v vs)).
    by rewrite free_predU1; apply/eqboolP; congr; congr.
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
