(* ==================================================================== *)
require import AllCore List Ring Int IntMin IntDiv Real RealExp Poly.
require import StdBigop StdPoly Binomial Counting Perms.
require import PolyDiv FiniteRing.
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


theory PolyFF.

  type coeff.

  clone import FiniteRing.FiniteField as FF with
    type t <= coeff.

  clone import Idomain as PID with
    type coeff <= coeff,
    theory IDC <- FF.F.

  import P.

  (*TODO: move this to polydiv.*)
  lemma unit_deg p :
    PolyComRing.unit p <=> deg p = 1.
  proof.
    rewrite PolyComRing.unitrP; split=> [[q] eq_|/P.deg_eq1 [c] [? ->>]]; last first.
    + by exists (P.polyC (F.invr c)); rewrite -P.polyCM F.mulVf.
    have neqp0: p <> poly0.
    + by apply/negP => ->>; move: eq_; rewrite PolyComRing.mulr0 eq_sym /= onep_neq0.
    have neqq0: q <> poly0.
    + by apply/negP => ->>; move: eq_; rewrite PolyComRing.mul0r eq_sym /= onep_neq0.
    move/(congr1 deg): (eq_); rewrite deg1 degM //.
    move/subr_eq0 => /=; move/subr_eq0; move: neqp0 neqq0.
    rewrite -!P.deg_eq0 !neq_ltz !(ltrNge _ 0) !P.ge0_deg !ltzE /=.
    move=> lep leq /eqz_leq [le_ _]; move: (ler_trans _ (1 + deg p) _ _ le_).
    + by apply/ler_add2r.
    by move/ler_subr_addl => /= ?; apply/eqz_leq.
  qed.

  op monic (p : poly) = lc p = F.oner.

  lemma monic_exp_scalp p q :
    monic q =>
    F.exp (P.lc q) (scalp p q) = F.oner.
  proof. by move=> ->; rewrite F.expr1z. qed.

  lemma monic1 :
    monic poly1.
  proof. by rewrite /monic lcC. qed.

  lemma monicC c :
    monic (P.polyC c) <=> c = F.oner.
  proof. by rewrite /monic lcC. qed.

  lemma monic_invrZ p :
    p <> poly0 =>
    monic (P.( ** ) (F.invr (P.lc p)) p).
  proof.
    move=> neq0; rewrite /monic lcZ_lreg.
    + by rewrite F.lregP F.invr_eq0 lc_eq0.
    by rewrite F.mulVr // -F.unitfE lc_eq0.
  qed.

  lemma monicM p q :
    monic p =>
    monic q =>
    monic (P.( * ) p q).
  proof. by rewrite /monic lcM => -> ->; rewrite F.mulr1. qed.

  lemma divp_eq p q :
    monic q =>
    p = (+) (P.( * ) (divp p q) q) (modp p q).
  proof.
    by move=> uq; rewrite -divp_eq monic_exp_scalp // scalepE PolyComRing.mul1r.
  qed.

  lemma dvdp_monic_divp p q :
    dvdp q p =>
    monic p =>
    monic q =>
    monic (divp p q).
  proof.
    move=> dvd_ up uq; move: (up); rewrite {1}(divp_eq p q) //.
    rewrite dvd_ PolyComRing.addr0.
    move: up uq; rewrite /monic => eqp eqq.
    by rewrite lcM eqq F.mulr1.
  qed.

  lemma monic_prod ['a] (P : 'a -> bool) F s :
    all (fun x => P x => monic (F x)) s =>
    monic (P.BigPoly.PCM.big P F s).
  proof.
    elim: s => [|x s IHs /= [+ /IHs u_ {IHs}]] /=.
    + by rewrite BigPoly.PCM.big_nil monic1.
    rewrite BigPoly.PCM.big_cons; case (P x) => //= _ ?.
    by apply/monicM.
  qed.

  lemma monic_exp p n :
    monic p =>
    monic (P.PolyComRing.exp p n).
  proof.
    move=> up; wlog: n / 0 <= n => [wlog|].
    + case (0 <= n) => [le0n|/ltrNge/oppr_gt0 lt0_].
      - by apply/wlog.
      move/ltzW: (lt0_) => le0_.
      rewrite -(opprK n) PolyComRing.exprN.
      case (P.deg p <= 1) => [/P.deg_le1 [c] ->>|].
      - rewrite polyCX //; move: up; rewrite /monic lcC => ->>.
        by rewrite F.expr1z PolyComRing.invr1 lcC.
      move=> /ltrNge lt1_; rewrite PolyComRing.unitout; [|by apply/wlog].
      apply/negP => unit_exp; move: (P.PolyComRing.unitrX_neq0 _ _ _ unit_exp).
      - by apply/gtr_eqF.
      by move/unit_deg => eq_; move: lt1_; rewrite eq_.
    elim: n => [|n le0n IHn]; [by rewrite PolyComRing.expr0 monic1|].
    by rewrite PolyComRing.exprSr // monicM.
  qed.

  lemma irreducible_poly_neq0 q :
    irreducible_poly q =>
    q <> poly0.
  proof.
    case=> [lt_ _]; rewrite -P.deg_eq0; apply/negP => eq_.
    by move: lt_; rewrite eq_.
  qed.
  (*TODO: end of move this to polydiv.*)


  (*TODO: rename and move this to polydiv*)
  lemma irreducible_poly_deg2 p :
    deg p = 2 =>
    irreducible_poly p.
  proof.
    move=> degp; rewrite /irreducible_poly degp /= => q.
    case/neq_ltz => [/ltzE/ler_subr_addr/P.deg_le0 ->>|].
    + by rewrite dvd0p => ->>; rewrite eqpxx.
    move=> lt_ dvdp_; rewrite -dvdp_size_eqp //.
    move: (dvdp_leq q p); rewrite -P.deg_eq0 degp dvdp_ /= => le_.
    by apply/ler_anti; rewrite le_ /=; apply/ltzS/ltr_subl_addr.
  qed.

  lemma poly1_or_dvdp_i p:
    deg p = 1 \/ exists q , irreducible_poly q /\ dvdp q p.
  proof.
    move: (P.ge0_deg p) (lerr (P.deg p)); move: {1 3}(P.deg p) => n le0n.
    elim: n le0n p => [|n le0n IHn] p.
    + move=> le_; right; exists X.
      move: (P.deg_eq0 p); rewrite eqz_leq le_ ge0_deg /= => ->>.
      by rewrite dvdp0 /= irreducible_poly_deg2 degX.
    move/ler_eqVlt=> [eq_|/ltzS/IHn //].
    move/ler_eqVlt: le0n => [<<-|lt0n]; [by rewrite eq_|].
    right; case: (irreducible_poly p) => [irr_|].
    + by exists p; rewrite irr_ dvdpp.
    rewrite /irreducible_poly andaE negb_and -lerNgt negb_forall.
    case=> [/P.deg_le1 [c] ->>|[q] /=].
    + move: eq_; rewrite degC ltr_eqF //=.
      by apply/ltr_subl_addr/(ler_lt_trans _ _ _ _ lt0n); case (_ = _).
    rewrite !negb_imply neq_ltz ltzE -ler_subr_addr deg_le0 => -[].
    case=> [->>|]; [by rewrite dvd0p // => -[->>]; rewrite eqpxx|].
    move=> lt1_ [dvdp_ Neqp_]; move/(_ q _): IHn.
    + move: (dvdp_leq _ _ _ dvdp_); [by rewrite -P.deg_eq0 eq_ gtr_eqF // ltzS ltzW|].
      move/dvdp_size_eqp: dvdp_; rewrite Neqp_ /= => neq_.
      case/ler_eqVlt; [by rewrite neq_|]; move/ltzE/ler_subr_addr => le_.
      by apply/(ler_trans _ _ _ le_); rewrite eq_.
    rewrite gtr_eqF //= => -[r] [irr_ dvdp__].
    exists r. rewrite (dvdp_trans _ _ _ dvdp__ dvdp_) /=.
    by move: irr_; rewrite /irreducible_poly.
  qed.

  lemma poly1_or_dvdp_iu p :
    monic p =>
    deg p = 1 \/ exists q , irreducible_poly q /\ monic q /\ dvdp q p.
  proof.
    move=> up; case: (poly1_or_dvdp_i p) => [-> //|].
    case=> q [irr_ dvdp_]; right; exists (P.( ** ) (F.invr (P.lc q)) q).
    split; split.
    + rewrite degZ_lreg; [|by case: irr_].
      by rewrite F.lregP F.invr_eq0 lc_eq0 irreducible_poly_neq0.
    + move=> lt1_ r degr dvd_rq; case: (irr_) => lt1q /(_ _ degr _).
      - by move: dvd_rq; rewrite dvdpZr // F.invr_eq0 lc_eq0 irreducible_poly_neq0.
      rewrite !(eqp_sym r); apply/eqp_trans/eqp_scale.
      by rewrite F.invr_eq0 lc_eq0 irreducible_poly_neq0.
    + by apply/monic_invrZ/irreducible_poly_neq0.
    move: dvdp_; rewrite dvdp_eq => eq_.
    apply/(eq_dvdp (F.( * ) (F.invr (P.lc q)) (F.exp (P.lc q) (scalp p q))) (divp p q)).
    + rewrite F.mulf_eq0 lc_expn_scalp_neq0 /= F.invr_eq0 lc_eq0 -P.deg_eq0.
      by apply/negP => eq__; move: irr_; rewrite /irreducible_poly eq__.
    by rewrite -scalerAr -eq_ scalepA.
  qed.

  op irreducible_monic_dec p qns =
    uniq (map fst qns) /\
    all (fun qn => let (q, n) = qn in irreducible_poly q /\ monic q /\ 0 < n) qns /\
    p = BigPoly.PCM.big predT (fun qn => let (q, n) = qn in PolyComRing.exp q n) qns.

  lemma irreducible_monic_dec_1 :
    irreducible_monic_dec poly1 [].
  proof. by rewrite /irreducible_monic_dec /= BigPoly.PCM.big_nil. qed.

  lemma monic_irreducible_monic_dec p :
    monic p <=> (exists qns , irreducible_monic_dec p qns).
  proof.
    split=> [up|[qns] [_ [all_ ->>]]]; last first.
    + apply/monic_prod; move: all_; apply/all_imp_in/allP.
      move=> [q n] mem_qn /= [_] [uq _] _.
      by apply/monic_exp.
    move: (P.ge0_deg p) (lerr (P.deg p)); move: {1 3}(P.deg p) => n le0n.
    elim: n le0n p up => [|n le0n IHn] p up.
    + by move/P.deg_le0 => ->>; move: up; rewrite /monic lc0 eq_sym F.oner_neq0.
    move/ler_eqVlt=> [eq_|/ltzS/(IHn _ up) //].
    move/ler_eqVlt: le0n => [<<-|lt0n].
    + case/P.deg_eq1: eq_ => ? [neqc0 ->>]; move: up; rewrite monicC => ->>.
      by exists []; apply/irreducible_monic_dec_1.
    case: (poly1_or_dvdp_iu _ up); [by rewrite eq_ -subr_eq0 /= => ->>|].
    case=> q [irr_] [u_ dvdp_]; move/(_ (divp p q) _ _): IHn.
    + by apply/dvdp_monic_divp.
    + rewrite size_divp.
      - rewrite -P.deg_eq0; apply/negP => eq__.
        by move: irr_; rewrite /irreducible_poly eq__.
      by rewrite eq_; smt.
    case=> qns.
    admit.
  qed.

  lemma perm_eq_irreducible_monic_dec p qns1 qns2 :
    irreducible_monic_dec p qns1 =>
    irreducible_monic_dec p qns2 =>
    perm_eq qns1 qns2.
  proof.
    case=> [uniq1] [all1 ->>] [uniq2] [all2].
    have all1_: all ((<) 0) (unzip2 qns1).
    + move: all1; rewrite all_map; apply/all_imp_in.
      by apply/allP => -[x n] /= mem_ [_] [_ lt0n]; rewrite /preim.
    have all2_: all ((<) 0) (unzip2 qns2).
    + move: all2; rewrite all_map; apply/all_imp_in.
      by apply/allP => -[x n] /= mem_ [_] [_ lt0n]; rewrite /preim.
    rewrite -perm_eq_debundle //.
    move: (perm_eq_bundle_debundle _ uniq1 all1_) => eq1.
    rewrite -(P.BigPoly.PCM.eq_big_perm _ _ _ _ eq1).
    move: (perm_eq_bundle_debundle _ uniq2 all2_) => eq2.
    rewrite -(P.BigPoly.PCM.eq_big_perm _ _ _ _ eq2).
    pose uqns1:= debundle qns1; pose uqns2:= debundle qns2.
    have allu1: all (predI irreducible_poly monic) uqns1.
    + apply/allP => q /mem_debundle [n] [lt0n mem_].
      by move/allP/(_ _ mem_): all1; rewrite /predI.
    have allu2: all (predI irreducible_poly monic) uqns2.
    + apply/allP => q /mem_debundle [n] [lt0n mem_].
      by move/allP/(_ _ mem_): all2; rewrite /predI.
    move=> {uniq1 uniq2 all1 all2 all1_ all2_ eq1 eq2}.
    move: uqns1 uqns2 allu1 allu2 => {qns1 qns2} qs1 qs2 all1 all2.
    rewrite !P.BigPoly.PCM.big_mapT; pose f1:= _ \o _; pose f2:= _ \o _.
    move: (P.BigPoly.PCM.big_undup predT idfun qs1).
    pose g1:= (fun a => _ (_ (_ a) qs1) (_ (_ a)) _).
    rewrite (P.BigPoly.PCM.eq_big_seq g1 f1) => [|<-].
    + move=> p; rewrite mem_undup => mem_p; rewrite /g1 /f1 /= => {f1 f2 g1}.
      rewrite /(\o) /idfun /= /P.PolyComRing.exp ltrNge count_ge0 /=.
      by rewrite PolyComRing.MulMonoid.iteropE.
    move: (P.BigPoly.PCM.big_undup predT idfun qs2).
    pose g2:= (fun a => _ (_ (_ a) qs2) (_ (_ a)) _).
    rewrite (P.BigPoly.PCM.eq_big_seq g2 f2) => [|<-].
    + move=> p; rewrite mem_undup => mem_p; rewrite /g2 /f2 /= => {f1 f2 g2}.
      rewrite /(\o) /idfun /= /P.PolyComRing.exp ltrNge count_ge0 /=.
      by rewrite PolyComRing.MulMonoid.iteropE.
    move: all1 all2 => {f1 f2 g1 g2}.
    elim: qs1 qs2 => [|q1 qs1 IHqs1 qs2]; [case=> [|q2 qs2] //=|].
    + rewrite BigPoly.PCM.big_nil BigPoly.PCM.big_cons.
      move=> [] [] [degq2 _] u_ _; rewrite /(predT q2) /(idfun q2) /=.
      pose q:= (P.BigPoly.PCM.big _ _ _); move: q => q /eq_sym.
      case (q = poly0) => [->>|neqq0].
      - by rewrite PolyComRing.mulr0 eq_sym PolyComRing.oner_neq0.
      move/(congr1 deg); rewrite degM // -?P.deg_ge1 ?ltzW //.
      rewrite deg1 -subr_eq0 /= subr_eq0 gtr_eqF //.
      move/P.deg_ge1: neqq0 => degq; rewrite addrC.
      by move: (ler_lt_add _ _ _ _ degq degq2).
    case=> [] [irr1 u1] all1 all2.
    rewrite BigPoly.PCM.big_cons /(predT q1) /(idfun q1) /= => eq_.
    have mem_: q1 \in qs2; last first.
    + move/(_ (rem q1 qs2) all1 _ _): IHqs1; [by apply/all_rem| |].
      - move: eq_; rewrite (P.BigPoly.PCM.big_rem _ _ _ _ mem_).
        rewrite /(predT q1) /(idfun q1) /=; move: (P.IDPoly.mulfI q1 _).
        * by apply/P.deg_gt0/ltzE/ltzW; case: irr1.
        by move=> inj_; apply/inj_.
      rewrite -(perm_cons q1) =>  perm_; apply/(perm_eq_trans _ _ _ perm_) => {perm_}.
      by apply/perm_eq_sym/perm_to_rem.
    move: eq_ => {IHqs1 all1}; pose r:= BigPoly.PCM.big _ _ _.
    pose q:= BigPoly.PCM.big _ _ _; move: r => r {qs1} eq_.
    move: (eq_dvdp F.oner r q1 q); rewrite F.oner_neq0.
    rewrite scalepE PolyComRing.mul1r PolyComRing.mulrC eq_ /= /q => {eq_ q}.
    elim: qs2 all2 => [|q2 qs2 IHqs2] /=.
    + by rewrite BigPoly.PCM.big_nil dvdp1 gtr_eqF; case: irr1.
    case=> [] [] irr2 u2 /IHqs2 {IHqs2} mem_.
    rewrite BigPoly.PCM.big_cons /(predT q2) /(idfun q2) /=.
    rewrite Gauss_dvdpor //; case=> [|_ /mem_ -> //] {mem_} dvdp12.
    case: irr2 => _ /(_ _ _ dvdp12) //; [by apply/gtr_eqF; case: irr1|].
    by move/eqp_eq; rewrite u1 u2 !scalepE !PolyComRing.mul1r.
  qed.
  (*TODO: end of rename and move this to polydiv*)




  op enum_ledeg_r (nps : int * poly list) =
    let (n, ps) = nps in
    (n + 1, allpairs (fun (p : poly) x => (+) (P.( ** ) x (P.polyXn n)) p) ps FF.FinType.enum).

  op enum_ledeg n =
    if 0 <= n
    then (iter n enum_ledeg_r (0, [P.poly0])).`2
    else [].

  op enum_deg n = filter (fun p => deg p = n) (enum_ledeg n).

  op enum_udeg n = filter monic (enum_deg n).

  op enum_iudeg n = filter irreducible_poly (enum_udeg n).
  
  lemma enum_ledeg_rP n :
    0 <= n =>
    (iter n enum_ledeg_r (0, [P.poly0])).`1 = n.
  proof.
    elim: n => [|n le0n]; [by rewrite iter0|].
    rewrite iterS //; pose nps:= iter _ _ _; move: nps => [? ps] /= ->>.
    by rewrite /enum_ledeg_r.
  qed.

  lemma enum_ledegP n p :
    p \in enum_ledeg n <=>
    (P.deg p <= n).
  proof.
    rewrite /enum_ledeg; case: (0 <= n) => [le0n|/ltrNge ltn0] /=; last first.
    + by apply/ltrNge/(ltr_le_trans _ _ _ ltn0)/P.ge0_deg.
    elim: n le0n p => [|n le0n +] p.
    + rewrite iter0 //= -P.deg_eq0; split=> [-> //|le_0].
      by apply/eqz_leq; rewrite le_0 ge0_deg.
    rewrite iterS //=; move: (enum_ledeg_rP _ le0n).
    pose nps:= iter _ _ _; move: nps => [? ps] /= ->>.
    rewrite /enum_ledeg_r /= => IHn; rewrite allpairsP /=.
    split=> [[] [q x] /= [/IHn le_] [_] ->> {IHn}|].
    + apply/(ler_trans _ _ _ (P.degD _ _))/ler_maxrP.
      split; [|by apply/ltzW/ltzS].
      apply/(ler_trans _ _ _ (P.degZ_le _ _)).
      by rewrite degXn; apply/ler_maxrP => /=; apply/addr_ge0.
    move=> le_; exists (P.(-) p (P.( ** ) (P."_.[_]" p n) (P.polyXn n)), "_.[_]" p n) => /=.
    rewrite FinType.enumP /= PolyComRing.addrA PolyComRing.addrAC.
    rewrite PolyComRing.subrr PolyComRing.add0r /= IHn => {IHn}.
    apply/P.deg_leP => // i leni; rewrite polyDE polyNE polyZE.
    rewrite polyXnE le0n /=; case/ler_eqVlt: leni => [<<- /=|ltni].
    + by rewrite F.mulr1 F.subrr.
    rewrite gtr_eqF //= F.mulr0 F.subr0; apply/P.gedeg_coeff.
    by apply/(ler_trans _ _ _ le_)/ltzE.
  qed.

  lemma uniq_enum_ledeg n :
    uniq (enum_ledeg n).
  proof.
    rewrite /enum_ledeg; case: (0 <= n) => [le0n|/ltrNge //].
    elim: n le0n => [|n le0n]; [by rewrite iter0|].
    rewrite iterS //=; move: (enum_ledeg_rP _ le0n) (enum_ledegP n).
    rewrite /enum_ledeg; pose nps:= iter _ _ _; move: nps => [? ps] /= ->>.
    rewrite le0n /= => mem_ps; rewrite /enum_ledeg_r /= => IHn.
    rewrite allpairs_uniq //=; [by apply/FinType.enum_uniq|].
    move=> p q x y /mem_ps le_p /mem_ps le_q _ _ {mem_ps} eq_.
    move: (congr1 (fun p => "_.[_]" p n) _ _ eq_) => /=.
    rewrite !P.polyDE !P.polyZE polyXnE le0n /= !F.mulr1.
    rewrite !P.gedeg_coeff // !F.addr0 => <<- /=.
    by move: (P.PolyComRing.addrI _ _ _ eq_).
  qed.

  lemma size_enum_ledeg n :
    0 <= n =>
    size (enum_ledeg n) = FinType.card ^ n.
  proof.
    move=> le0n; rewrite /card_ledeg /enum_ledeg le0n /=.
    elim: n le0n => [|n le0n]; [by rewrite iter0 //= expr0|].
    rewrite iterS //=; move: (enum_ledeg_rP _ le0n).
    pose nps:= iter _ _ _; move: nps => [? ps] /= ->>.
    move=> eq_; rewrite /enum_ledeg_r /= size_allpairs eq_.
    by rewrite /FinType.card exprSr.
  qed.

  lemma enum_degP n p :
    p \in enum_deg n <=>
    (P.deg p = n).
  proof. by rewrite /enum_deg mem_filter /= enum_ledegP; split. qed.

  lemma uniq_enum_deg n :
    uniq (enum_deg n).
  proof. by rewrite /enum_deg; apply/filter_uniq/uniq_enum_ledeg. qed.

  lemma perm_eq_enum_deg n :
    perm_eq (enum_ledeg n) ((enum_ledeg (n - 1)) ++ (enum_deg n)).
  proof.
    apply/uniq_perm_eq.
    + by apply/uniq_enum_ledeg.
    + rewrite cat_uniq uniq_enum_ledeg uniq_enum_deg hasPn /=.
      by move=> p /enum_degP <<-; rewrite enum_ledegP -ltzS.
    move=> p; rewrite mem_cat !enum_ledegP enum_degP.
    by rewrite -(ltzS _ (n - 1)) /= orbC -ler_eqVlt.
  qed.

  lemma size_enum_deg n :
    0 < n =>
    size (enum_deg n) = (FinType.card - 1) * FinType.card ^ (n - 1).
  proof.
    move=> lt0n; rewrite /card_deg.
    move/perm_eq_size: (perm_eq_enum_deg n).
    rewrite size_cat !size_enum_ledeg; [by apply/ltzW|by apply/ltzS|].
    rewrite (addrC _ (size _)) -subr_eq => <-.
    by rewrite mulrDl -exprS; [apply/ltzS|rewrite /= mulNr].
  qed.

  lemma enum_udegP n p :
    p \in enum_udeg n <=>
    (monic p /\ deg p = n).
  proof. by rewrite /enum_udeg mem_filter enum_degP. qed.

  lemma uniq_enum_udeg n :
    uniq (enum_udeg n).
  proof. by rewrite filter_uniq; apply/uniq_enum_deg. qed.

  lemma perm_eq_enum_udeg n :
    0 < n =>
    perm_eq (enum_udeg n) (map (fun p => (+) (P.polyXn (n - 1)) p) (enum_ledeg (n - 1))).
  proof.
    move=> lt0n; apply/uniq_perm_eq.
    + by apply/uniq_enum_udeg.
    + apply/map_inj_in_uniq; [|by apply/uniq_enum_ledeg].
      move=> p q /enum_ledegP le_p /enum_ledegP le_q /=.
      by apply/P.PolyComRing.addrI.
    move=> p; rewrite enum_udegP /= mapP.
    split=> [[up eq_p]|].
    + exists (P.(-) p (P.polyXn (n - 1))).
      rewrite enum_ledegP PolyComRing.addrA PolyComRing.addrAC.
      rewrite PolyComRing.subrr PolyComRing.add0r /=.
      apply/P.deg_leP; [by apply/ltzS|].
      move=> i; rewrite polyDE polyNE polyXnE -(ltzS _ (n - 1)) lt0n /=.
      case/ler_eqVlt => [<<-/=|lt_]; [by rewrite F.subr_eq0 -eq_p up|].
      rewrite gtr_eqF //= F.subr0; apply/P.gedeg_coeff; rewrite eq_p.
      by move/ltzE: lt_.
    case=> q [/enum_ledegP le_ ->>]; rewrite /monic degDl.
    + by rewrite degXn ler_maxr //=; [apply/ltzW|move/ltzS: le_].
    rewrite degXn /= ler_maxr; [by apply/ltzW|].
    rewrite polyDE polyXnE /= -ltzS lt0n /= F.addrC -F.subr_eq0.
    by rewrite -F.addrA F.subrr F.addr0; apply/P.gedeg_coeff.
  qed.

  lemma size_enum_udeg n :
    0 < n =>
    size (enum_udeg n) = FinType.card ^ (n - 1).
  proof.
    move=> lt0n; rewrite /card_udeg.
    move/perm_eq_size: (perm_eq_enum_udeg _ lt0n) => ->.
    by rewrite size_map size_enum_ledeg // -ltzS.
  qed.

  lemma enum_iudegP n p :
    p \in enum_iudeg n <=>
    (irreducible_poly p /\ monic p /\ deg p = n).
  proof. by rewrite /enum_iudeg mem_filter enum_udegP. qed.

  lemma uniq_enum_iudeg n :
    uniq (enum_iudeg n).
  proof. by rewrite filter_uniq; apply/uniq_enum_udeg. qed.

end PolyFF.



theory Counting_Argument.

  import SIterOp.
  import PolyReal.
  import PrePolyReal.BigCf.
  import BigPoly.
  import Bigint.
  import Bigreal.

  op poly_prod_conseq p n =
    PCM.bigi predT (fun j => p + polyC j%r) 0 n.

  op poly_bin p n =
    poly_prod_conseq p n * polyC (1%r / (fact n)%r).

  op poly_prod_bin k m s =
    PCM.bigi predT (fun i => poly_bin (m i) (nth 0 s (i - 1))) 1 (k + 1).

  op sPI k m =
    polyXn k -
    PCA.big predT
      (poly_prod_bin k m)
      (rem (shape k (cc_perm k)) (allshapes k)).

  op PI (n : int) = siter n sPI poly1.

  op is_fromint (x : real) = exists n, x = n%r.

  lemma is_fromintP x :
    is_fromint x <=> ((floor x)%r = x).
  proof. by split=> [[?] ->>|<-]; [rewrite from_int_floor|exists (floor x)]. qed.

  lemma is_fromint_fromint n :
    is_fromint n%r.
  proof. by exists n. qed.

  lemma is_fromintD x y :
    is_fromint x => is_fromint y => is_fromint (x + y).
  proof. by case=> nx ->> [ny] ->>; exists (nx + ny); rewrite fromintD. qed.

  lemma is_fromintN x :
    is_fromint x => is_fromint (-x).
  proof. by case=> nx ->>; exists (-nx); rewrite fromintN. qed.

  lemma is_fromintB x y :
    is_fromint x => is_fromint y => is_fromint (x - y).
  proof. by move=> ? ?; apply/is_fromintD => //; apply/is_fromintN. qed.

  lemma is_fromintM x y :
    is_fromint x => is_fromint y => is_fromint (x * y).
  proof. by case=> nx ->> [ny] ->>; exists (nx * ny); rewrite fromintM. qed.

  lemma is_fromint_exp x n :
    0 <= n => is_fromint x => is_fromint (x ^ n).
  proof. by move=> le0n [nx] ->>; rewrite RField.fromintXn // is_fromint_fromint. qed.

  lemma is_fromint_sum ['a] P F (r : 'a list) :
    all (fun x => P x => is_fromint (F x)) r =>
    is_fromint (PrePolyReal.BigCf.BRA.big P F r).
  proof.
    elim: r => [|x r IHr /= []]; [by rewrite PrePolyReal.BigCf.BRA.big_nil is_fromint_fromint|].
    rewrite PrePolyReal.BigCf.BRA.big_cons.
    by case (P x) => //= Px is_fromintFx /IHr; apply/is_fromintD.
  qed.

  lemma is_fromint_prod ['a] P F (r : 'a list) :
    all (fun x => P x => is_fromint (F x)) r =>
    is_fromint (PrePolyReal.BigCf.BRM.big P F r).
  proof.
    elim: r => [|x r IHr /= []]; [by rewrite PrePolyReal.BigCf.BRM.big_nil is_fromint_fromint|].
    rewrite PrePolyReal.BigCf.BRM.big_cons.
    by case (P x) => //= Px is_fromintFx /IHr; apply/is_fromintM.
  qed.

  lemma dvd_fact_prod_range (m n d : int) :
    d <= n - m =>
    fact d %| BIM.bigi predT idfun m n.
  proof.
    move=> led_; case (0 < d) => [lt0d|/lerNgt led0]; [|by rewrite fact0].
    case (0 < m) => [lt0m|/lerNgt lem0].
    + rewrite (range_cat (n - d)); [by apply/ler_subr_addr/ler_subr_addl| |].
      - by apply/ler_subl_addr/ler_subl_addl/ltzW.
      rewrite BIM.big_cat dvdz_mull; have ledn {m led_ lt0m}: d < n.
      - by apply/(ltr_le_trans (m + d)); [apply/ltr_subl_addr|apply/ler_subr_addl].
      apply/dvdzP; exists (bin (n - 1) d); rewrite eq_sym mulrC.
      apply/(mulfI (fact (n - 1 - d))); [by apply/gtr_eqF/fact_gt0|].
      rewrite mulrA (mulrC (fact _)) eq_bin_div.
      - by split=> [|_]; [apply/ltzW|apply/ltzS].
      rewrite addrAC /fact /= -BIM.big_cat_int //.
      - by apply/ltzS/ltr_subl_addr => /=; apply/subr_gt0.
      by apply/ler_subl_addr/ler_subl_addl/ltzW.
    case (0 < n) => [lt0n|/lerNgt len0].
    + case: (Bigint.prodr_eq0 predT idfun (range m n)) => /(_ _).
      - by exists 0; rewrite /predT /idfun mem_range lem0 lt0n.
      by move => -> _; apply/dvdz0.
    rewrite (range_cat (m + d)); [by apply/ler_subl_addl/ltzW| |].
    + by apply/ler_subr_addl.
    rewrite BIM.big_cat dvdz_mulr; have {n led_ len0} led_: d <= -m.
    + by apply/(ler_trans _ _ _ led_)/ler_subr_addr.
    apply/dvdzP; exists ((-1) ^ d * bin (-m) d); rewrite eq_sym mulrC.
    apply/(mulfI (fact (-m - d))); [by apply/gtr_eqF/fact_gt0|].
    rewrite !mulrA (mulrAC _ _ (bin _ _)) (mulrC (fact _)) eq_bin_div.
    + by split=> //; apply/ltzW.
    rewrite /fact (range_cat (-m - d + 1)).
    + by apply/ler_subl_addr/subr_ge0.
    + by apply/ler_add2r/ler_subl_addl/ler_subl_addr/ltzW.
    rewrite Bigint.BIM.big_cat -mulrA; congr.
    move: (Bigint.mulr_const (range ((-m) - d + 1) ((-m) + 1)) (-1)).
    rewrite size_range opprD (addrAC _ 1) !addrA /= opprD addrA /= ler_maxr ?ltzW // => <-.
    rewrite -BIM.big_split (BIM.eq_big_perm _ idfun _ (map Int.([-]) (range (-m - d + 1) (-m + 1)))).
    + apply/uniq_leq_size_perm_eq; [by apply/range_uniq| | |].
      - by apply/uniq_map_injective; [apply/oppr_inj|apply/range_uniq].
      - by move=> k mem_k; apply/mapP; exists (-k) => /=; apply/mem_range_opp; rewrite !opprD /=.
      by rewrite size_map !size_range !opprD !addrA !(addrAC _ 1) /= addrAC.
    by rewrite BIM.big_mapT; apply/BIM.eq_big_seq => k mem_k; rewrite /(\o) /idfun /= mulrN1.
  qed.

  lemma poly_bin_int k p n :
    (n = 0) \/ is_fromint (peval p k%r) =>
    is_fromint (peval (poly_bin p n) k%r).
  proof.
    case=> [->>|all_].
    + rewrite /poly_bin /poly_prod_conseq range_geq //.
      rewrite PCM.big_nil PolyComRing.mul1r fact0 //.
      by rewrite StdOrder.RealOrder.Domain.divrr // peval1 is_fromint_fromint.
    rewrite pevalM peval_prod pevalC /=.
    pose F:= idfun \o ((+) (floor (peval p k%r))).
    rewrite (Bigreal.BRM.eq_big_seq _ (fun y => (F y)%r) _); last first.
    + rewrite -Bigreal.prodr_ofint -fromint_div ?is_fromint_fromint //.
      rewrite -BIM.big_mapT -range_add /= dvd_fact_prod_range.
      by rewrite -addrA -ler_subl_addl.
    move=> j mem_j; rewrite /F /(\o) /idfun /= => {F}.
    by rewrite pevalD pevalC fromintD; congr; rewrite eq_sym -is_fromintP.
  qed.

  lemma poly_prod_bin_int n k m s :
    0 <= n =>
    (forall j , j \in range 1 (n + 1) => (nth 0 s (j - 1) = 0) \/ is_fromint (peval (m j) k%r)) =>
    is_fromint (peval (poly_prod_bin n m s) k%r).
  proof.
    move=> le0n all_; rewrite peval_prod.
    apply/is_fromint_prod/allP => j /= mem_j _.
    by apply/poly_bin_int/all_.
  qed.

  lemma PI_int (n k : int) :
    is_fromint (peval (PI n) k%r).
  proof.
    rewrite/PI; case (n <= 0) => [ltn0|/ltrNge].
    + by rewrite siter0 // peval1 is_fromint_fromint.
    rewrite -(subrK n 1); move: (n - 1) => {n} n /ltzS.
    elim/sintind: n => n le0n IHn; rewrite siterS //= /(sPI (n + 1)).
    rewrite pevalB pevalXn peval_sum is_fromintB.
    + by case (0 <= n + 1) => [le_|_]; [apply/is_fromint_exp => //|]; apply/is_fromint_fromint.
    apply/is_fromint_sum/allP => /= s mem_s _ /=.
    apply/poly_prod_bin_int; [by apply/addr_ge0|].
    move=> j /= mem_j; rewrite le2_mem_range.
    move: mem_j; rewrite (rangeSr 1 (n + 1)); [by apply/ler_subl_addr|].
    rewrite mem_rcons /=; case => [->>|mem_j].
    + left => /=.
      (*TODO: permutations lemma.*)
      admit.
    rewrite range_ltn /=; [by apply/ltzS|rewrite mem_j /=].
    right; move: mem_j; rewrite -(subrK j 1); move: (j - 1) => {j} j.
    by rewrite mem_range_addr /= => mem_j; apply/IHn/mem_range.
  qed.

  lemma ledeg_poly_prod_conseq p k n :
    0 < k =>
    0 <= n =>
    deg p <= k + 1 =>
    deg (poly_prod_conseq p n) <= k * n + 1.
  proof.
    move=> lt0k le0n le_; apply/(ler_trans _ _ _ (BigPoly.deg_prod_le _ _ _)) => /=.
    case: (all _ _) => /=; [|by apply/addr_ge0 => //; apply/mulr_ge0 => //; apply/ltzW].
    apply/ler_add2r; move: (Bigint.bigi_constz k 0 n _) => //= <-.
    apply/Bigint.ler_sum_seq => i mem_i _; rewrite /(\o) /=.
    apply/ler_subl_addr/(ler_trans _ _ _ (degD _ _))/ler_maxrP; split=> //.
    rewrite degC -ltzS /= -ltr_subl_addr; apply/(ler_lt_trans _ _ _ _ lt0k).
    by case (_ = _).
  qed.

  lemma ledeg_poly_bin p k n :
    0 < k =>
    0 <= n =>
    deg p <= k + 1 =>
    deg (poly_bin p n) <= k * n + 1.
  proof.
    move=> lt0k le0n le_; rewrite -(ler_add2r 1) /=.
    apply/(ler_trans _ _ _ (degM_le_or _ _ _)).
    + right; rewrite eq_polyC0 RField.div1r RField.invr_eq0.
      by rewrite eq_fromint gtr_eqF // fact_gt0.
    rewrite degC RField.div1r RField.invr_eq0 eq_fromint gtr_eqF ?fact_gt0 //=.
    by apply/ler_subr_addr => /=; apply/ledeg_poly_prod_conseq.
  qed.

  lemma ledeg_poly_prod_bin n m s :
    0 <= n =>
    is_shape (n + 1) s =>
    (forall j , j \in range 1 (n + 2) => deg (m j) <= j + 1) =>
    deg (poly_prod_bin (n + 1) m s) <= n + 2.
  proof.
    move=> le0n is_s_s le_; apply/(ler_trans _ _ _ (BigPoly.deg_prod_le _ _ _)) => /=.
    case: (all _ _) => /=; [apply/ler_subr_addr => /=|by apply/addr_ge0].
    apply/(ler_trans _ _ _ (Bigint.ler_sum_seq _ _ (fun i => i * (nth 0 s (i - 1))) _ _)).
    + move=> k mem_k _; rewrite {1}/(\o) /= -(ler_add2r 1) /=.
      apply/ledeg_poly_bin; [by move: mem_k; apply/mem_range_lt| |by apply/le_].
      case/is_shapeP: is_s_s => p [is_p_p <<-].
      apply/nth_shape_ge0; move: (size_is_perm _ _ _ is_p_p); [by apply/addr_ge0|].
      by move=> ->; apply/mem_range_subr.
    by apply/lerr_eq; rewrite (is_shape_sum _ _ _ is_s_s) // addr_ge0.
  qed.

  lemma ledeg_PI n :
    0 <= n =>
    deg (PI (n + 1)) <= n + 2.
  proof.
    rewrite/PI; elim/sintind: n => n le0n IHn.
    rewrite siterS //= {1}/sPI.
    apply/(ler_trans _ _ _ (degB _ _)); rewrite degXn /= (ler_maxr 0); [by apply/addr_ge0|].
    apply/ler_maxrP => /=; rewrite PCA.big_seq; apply/BigPoly.deg_sum; [by apply/addr_ge0|].
    move=> s; rewrite /= rem_filter; [by apply/allshapes_uniq|].
    move=> /mem_filter; rewrite {1}/predC1 /= => -[neqp /allshapesP is_shape_p].
    apply/ledeg_poly_prod_bin => // j /= mem_j; rewrite !le2_mem_range.
    move: mem_j; rewrite (rangeSr 1 (n + 1)); [by apply/ler_subl_addr|].
    rewrite mem_rcons /=; case=> [->>|mem_j].
    + by rewrite mem_range /= deg1 -ler_subl_addr; move: le0n; apply/ler_trans.
    rewrite range_ltn /=; [by apply/ltzS|].
    rewrite mem_j /=; move: mem_j.
    rewrite -(subrK j 1); move: (j - 1) => {j} j /=.
    by rewrite mem_range_addr /= => mem_j; apply/IHn/mem_range.
  qed.

  lemma lc_poly_prod_conseq p n :
    0 <= n =>
    lc (poly_prod_conseq p n) =
    if 1 < deg p
    then (lc p) ^ n
    else Bigreal.BRM.bigi predT (fun (j : int) => lc p + j%r) 0 n.
  proof.
    rewrite /poly_prod_conseq lc_prod => le0n.
    move: (deg_le1 p); rewrite ltrNge; case (deg p <= 1) => //=.
    + move=> ledeg1 [c] ->>; rewrite lcC.
      apply/Bigreal.BRM.eq_big_int => i /mem_range mem_i.
      by rewrite /(\o) -polyCD lcC.
    move/ltrNge=> lt1deg _.
    rewrite (Bigreal.BRM.eq_big_int _ _ _ (fun _ => lc p)); last first.
    + by rewrite Bigreal.mulr_const size_range ler_maxr.
    move=> i _; rewrite /(\o) /= lcDl // degC.
    by move: lt1deg; apply/ler_lt_trans; case (_ = _).
  qed.

  lemma eqdeg_poly_prod_conseq p n :
    0 <= n =>
    deg (poly_prod_conseq p n) =
    if (all (fun c => p + polyC c%r <> poly0) (range 0 n))
    then n * (deg p - 1) + 1
    else 0.
  proof.
    move=> le0n; rewrite /poly_prod_conseq deg_prod.
    pose b1:= all _ _; pose b2:= all _ _; have: b1 = b2.
    + rewrite /b1 /b2 eq_iff; apply/eq_all_in => c mem_c.
      by rewrite /predC /predI /predT.
    move=> <- {b2}; case: b1; rewrite /b1 => {b1} //.
    move=> all_; congr.
    rewrite (BIA.eq_big_int _ _ _ (fun _ => deg p - 1)); last first.
    + by rewrite big_constz count_predT size_range mulrC ler_maxr.
    move=> i /mem_range mem_i; rewrite /(\o) /=; congr.
    move: all_ (all_) => /allP /(_ 0) + /allP /(_ _ mem_i).
    rewrite /predC /predI /predT /= mem_range /= PolyComRing.addr0.
    case/ler_eqVlt: le0n => [<<-|lt0n]; [by move: mem_i; rewrite range_geq|].
    rewrite lt0n /=; move: (deg_le1 p); case: (deg p <= 1) => /=.
    + by move=> _ [c] ->>; rewrite -polyCD !eq_polyC0 !degC => -> ->.
    move=> /ltrNge lt1deg _ _ _; rewrite degDl // degC.
    by move: lt1deg; apply/ler_lt_trans => //; case (_ = _).
  qed.

  lemma neqpoly0_poly_prod_conseq p n :
    0 <= n =>
    (all (fun c => p + polyC c%r <> poly0) (range 0 n)) =>
    poly_prod_conseq p n <> poly0.
  proof.
    move=> le0n all_; rewrite -deg_eq0 eqdeg_poly_prod_conseq //.
    rewrite all_ //=; apply/gtr_eqF/ltzS; case/ler_eqVlt: le0n => [<<- //|lt0n].
    apply/mulr_ge0; [by apply/ltzW|]; apply/subr_ge0; move: all_.
    move => /allP /(_ 0); rewrite mem_range lt0n /= PolyComRing.addr0.
    by rewrite -deg_eq0; case/ler_eqVlt: (ge0_deg p) => [<-//|/ltzE].
  qed.

  lemma lc_poly_bin p n :
    0 <= n =>
    lc (poly_bin p n) =
    if 1 < deg p
    then ((lc p) ^ n) / (fact n)%r
    else Bigreal.BRM.bigi predT (fun (j : int) => lc p + j%r) 0 n / (fact n)%r.
  proof.
    by move=> le0n; rewrite /poly_bin lcM lc_poly_prod_conseq // lcC; case (1 < deg p).
  qed.

  lemma eqdeg_poly_bin p n :
    0 <= n =>
    deg (poly_bin p n) =
    if (all (fun c => p + polyC c%r <> poly0) (range 0 n))
    then n * (deg p - 1) + 1
    else 0.
  proof.
    move=> le0n; rewrite /poly_bin; pose b:= all _ _; case: b; rewrite /b => {b}.
    + move=> all_; rewrite degM.
      - by apply/neqpoly0_poly_prod_conseq.
      - rewrite eq_polyC0 RField.mul1r RField.unitrV eq_fromint.
        by apply/gtr_eqF/fact_gt0.
      rewrite degC RField.mul1r StdOrder.RealOrder.Domain.invr_eq0.
      rewrite eq_fromint (gtr_eqF _ 0) //=; [by rewrite fact_gt0|].
      by rewrite eqdeg_poly_prod_conseq // all_.
    move=> Nall_; move: (eqdeg_poly_prod_conseq p _ le0n); rewrite Nall_ /=.
    by rewrite deg_eq0 => ->; rewrite PolyComRing.mul0r deg0.
  qed.

  lemma neqpoly0_poly_bin p n :
    0 <= n =>
    (all (fun c => p + polyC c%r <> poly0) (range 0 n)) =>
    poly_bin p n <> poly0.
  proof.
    move=> le0n all_; rewrite /poly_bin; apply/IDPoly.mulf_neq0.
    + by apply/neqpoly0_poly_prod_conseq.
    rewrite eq_polyC0 RField.mul1r RField.unitrV eq_fromint.
    by apply/gtr_eqF/fact_gt0.
  qed.

  lemma lc_poly_prod_bin n m s :
    0 <= n =>
    is_shape (n + 1) s =>
    (forall j , j \in range 1 (n + 2) => (nth 0 s (j - 1) = 0) \/ 1 < deg (m j)) =>
    lc (poly_prod_bin (n + 1) m s) =
    Bigreal.BRM.bigi predT
      (fun j => ((lc (m j)) ^ (nth 0 s (j - 1))) / (fact (nth 0 s (j - 1)))%r)
      1 (n + 2).
  proof.
    move=> le0n is_shape_ or_.
    rewrite /poly_prod_bin lc_prod /=.
    apply/Bigreal.BRM.eq_big_seq => j mem_j; rewrite /(\o) /=.
    rewrite lc_poly_bin; last first.
    + move: or_ => /(_ _ mem_j) /or_andl; case=> [[-> ->] /=|-> //].
      by rewrite range_geq // Bigreal.BRM.big_nil fact0 // RField.expr0.
    (*TODO: permutations lemma.*)
    admit.
  qed.

  lemma eqdeg_poly_prod_bin n m s :
    0 <= n =>
    is_shape (n + 1) s =>
    deg (poly_prod_bin (n + 1) m s) =
    if (all (fun j => all (fun c => m j + polyC c%r <> poly0) (range 0 (nth 0 s (j - 1)))) (range 1 (n + 2)))
    then BIA.bigi predT (fun j => (nth 0 s (j - 1)) * (deg (m j) - 1)) 1 (n + 2) + 1
    else 0.
  proof.
    move=> le0n is_shape_; rewrite /poly_prod_bin.
    pose b:= (all _ _); case: b; rewrite /b => {b}.
    + move=> /allP all_; rewrite deg_prod /=.
      pose b:= (all _ _); have: b; rewrite /b => {b}.
      - apply/allP => j mem_j; rewrite /predC /predI /predT /=.
        apply/neqpoly0_poly_bin; [|by apply/all_].
        (*TODO: permutations lemma.*)
        admit.
      move=> -> /=; congr; apply/BIA.eq_big_seq => j mem_j.
      rewrite /(\o) /= eqdeg_poly_bin; [|by move/(_ _ mem_j): all_ => /= ->].
      (*TODO: permutations lemma.*)
      admit.
    rewrite -has_predC => /hasP [j] [mem_j]; rewrite /predC /=.
    rewrite -has_predC => /hasP [c] [mem_c]; rewrite /predC /= => eq_.
    apply/deg_eq0/BigPoly.prodr0; exists j; rewrite /predT mem_j /=.
    apply/deg_eq0; rewrite eqdeg_poly_bin; last first.
    + pose b:= all _ _; have: !b; rewrite /b => {b}; [|by move=> ->].
      by rewrite -has_predC; apply/hasP; exists c; split.
    (*TODO: this lemma needs to be changed.*)
    admit.
  qed.

  lemma coeff_PI n :
    0 <= n =>
    (PI (n + 1)).[(n + 1)] = 1%r / (n + 1)%r.
  proof.
    rewrite/PI; elim/sintind: n => n le0n IHn; rewrite siterS // /(sPI (n + 1)).
    have {IHn} IHn: forall (j : int), j \in range 1 (n + 1) =>
                                      (siter j sPI poly1).[j] = (1%r / j%r) /\
                                      lc (siter j sPI poly1) = (1%r / j%r) /\
                                      deg (siter j sPI poly1) = j + 1.
    + move=> j mem_j; move: (IHn (j - 1)); rewrite /= -mem_range mem_range_subr mem_j /=.
      move=> coeff_; rewrite coeff_ /= and_impl; split => [->//|]; apply/ltdeg_neq0coeff.
      - move: (ledeg_PI (j - 1) _); [|by rewrite /PI].
        by apply/ler_subr_addr; move: mem_j; apply/mem_range_le.
      by rewrite coeff_ RField.unitrV eq_fromint gtr_eqF //; move: mem_j; apply/mem_range_lt.
    rewrite polyDE polyNE polyXnE /= addr_ge0 // /b2i /= polysumE.
    rewrite rem_filter; [by apply/allshapes_uniq|].
    rewrite (Bigreal.BRA.eq_big_seq _
              (fun s =>
                Bigreal.BRM.bigi predT
                  (fun j => 1%r / ( j ^ nth 0 s (j - 1) * fact (nth 0 s (j - 1)) )%r )
                  1 (n + 2)) ).
    + move=> s /=; case/mem_filter; rewrite /predC1.
      move=> neqs_ /allshapesP is_s_s; rewrite -lcP /=.
      - rewrite eqdeg_poly_prod_bin //.
        pose b:= all _ _; have: b; rewrite /b => {b} [|all_].
        * apply/allP => j mem_j /=; apply/allP => c mem_c /=.
          rewrite le2_mem_range range_ltn /=; [by apply/ltzS|].
          move: mem_j; rewrite (rangeSr _ (n + 1)); [by apply/ler_subl_addr|].
          rewrite mem_rcons /=; case=> [->>|mem_j].
          + rewrite gtr_eqF /=; [by apply/ltzS|].
            rewrite mem_range /= -polyCD eq_polyC0.
            rewrite -fromintD eq_fromint gtr_eqF //.
            by apply/ltr_subl_addl; move: mem_c; apply/mem_range_lt.
          rewrite mem_j /=; case/(_ _ mem_j): IHn => _ [_ deg_]; rewrite -deg_eq0; apply/gtr_eqF.
          by rewrite degDl deg_ ?degC -ltr_subl_addr; move: mem_j; apply/mem_range_lt => //; case (_ = _).
        rewrite all_ /= -subr_eq0 addrAC opprD !addrA /= -addrA -opprD subr_eq0.
        rewrite -(is_shape_sum _ _ _ is_s_s) /=; [by apply/addr_ge0|].
        apply/BIA.eq_big_seq => j mem_j /=; rewrite le2_mem_range mulrC.
        rewrite range_ltn /=; [by apply/ltzS|]; move: mem_j.
        rewrite (rangeSr _ (n + 1)); [by apply/ler_subl_addr|].
        rewrite mem_rcons /=; case=> [->>|mem_j]; last first.
        * by rewrite mem_j /=; case/(_ _ mem_j): IHn => _ [_ ->].
        rewrite /= mem_range /= (gtr_eqF _ 0) /=; [by apply/ltzS|].
        rewrite deg1 /= eq_sym mulrI_eq0; [by apply/lregP/gtr_eqF/ltzS|].
        (*TODO: permutations lemma.*)
        move: neqs_.
        admit.
      rewrite lc_poly_prod_bin //.
      - move=> j mem_j /=; rewrite le2_mem_range.
        rewrite range_ltn /=; [by apply/ltzS|]; move: mem_j.
        rewrite (rangeSr _ (n + 1)); [by apply/ler_subl_addr|].
        rewrite mem_rcons /=; case=> [->>/=|mem_j]; last first.
        * rewrite mem_j /=; case/(_ _ mem_j): IHn => _ [_ ->].
          by rewrite -ltr_subl_addr; right; move: mem_j; apply/mem_range_lt.
        rewrite mem_range /= (gtr_eqF (_ + 1) 0) /=; [by apply/ltzS|].
        rewrite deg1 /=.
        (*TODO: permutations lemma.*)
        move: neqs_.
        admit.
      apply/Bigreal.BRM.eq_big_seq => j mem_j /=; rewrite le2_mem_range.
      rewrite range_ltn /=; [by apply/ltzS|]; move: mem_j.
      rewrite (rangeSr _ (n + 1)); [by apply/ler_subl_addr|].
      rewrite mem_rcons /=; case=> [->>/=|mem_j]; last first.
      - rewrite mem_j /=; case/(_ _ mem_j): IHn => _ [-> _].
        rewrite -rpow_int.
        * apply/StdOrder.RealOrder.divr_ge0 => //.
          by rewrite le_fromint; move: mem_j; apply/mem_range_le.
        rewrite rpowMVr //; [by rewrite lt_fromint //; move: mem_j; apply/mem_range_lt|].
        rewrite rpow1r RField.mul1r fromintM RField.invfM rpow_int.
        * by rewrite le_fromint; move: mem_j; apply/mem_range_le.
        rewrite -RField.fromintXn //.
        (*TODO: permutations lemma.*)
        admit.
      rewrite mem_range /= (gtr_eqF (_ + 1) 0) /=; [by apply/ltzS|].
      rewrite lc1 /= RField.expr1z RField.mul1r fromintM RField.invfM.
      apply/(RField.mulrI (fact (nth 0 s n))%r).
      - by rewrite eq_fromint; apply/gtr_eqF/fact_gt0.
      rewrite RField.mulrA RField.mulrAC RField.divff.
      - by rewrite eq_fromint; apply/gtr_eqF/fact_gt0.
      rewrite RField.mul1r eq_sym RField.invr_eq1.
      (*TODO: permutations lemma.*)
      move: neqs_.
      admit.
    rewrite Bigreal.BRA.big_filter (Bigreal.BRA.eq_bigl _ (predC (pred1 (shape (n + 1) (cc_perm (n + 1)))))).
    + by move=> ?; rewrite /predC1 /predC /pred1.
    rewrite -RField.subr_eq0 -RField.addrA -RField.opprD RField.subr_eq0 eq_sym RField.addrC.
    pose P:= pred1 _; pose s:= allshapes _.
    pose f:= (fun s => Bigreal.BRM.bigi _ (fun j => (_ / (j ^ _ _ s (j - 1) * _ (_ _ s (j - 1)))%r)) _ _).
    move: (Bigreal.BRA.bigEM P f s); have ->: Bigreal.BRA.big P f s = inv (n + 1)%r.
    + rewrite -Bigreal.BRA.big_filter /P => {P}; rewrite filter_pred1 count_uniq_mem /s => {s}.
      - by apply/allshapes_uniq.
      pose b:=(_ \in _); have: b; rewrite /b => {b} [|->].
      - by rewrite -allshapesP is_shapeP; exists (cc_perm (n + 1)) => /=; apply/is_perm_cc.
      rewrite b2i1 nseq1 Bigreal.BRA.big_seq1 /f => {f}.
      (*TODO: permutations lemma.*)
      admit.
    move=> <-; rewrite /P /f /s => {P f s}.
    (*TODO: permutations lemma.*)
    admit.
  qed.

  lemma eqdeg_PI n :
    0 <= n =>
    deg (PI (n + 1)) = n + 2.
  proof.
    move=> le0n; apply/(ltdeg_neq0coeff (PI (n + 1)) (n + 1)).
    + by apply/ledeg_PI.
    by rewrite coeff_PI // RField.mul1r RField.unitrV eq_fromint gtr_eqF //; apply/ltzS.
  qed.

  lemma lc_PI n :
    0 <= n =>
    lc (PI (n + 1)) = 1%r / (n + 1)%r.
  proof. by move=> le0n; rewrite eqdeg_PI //= coeff_PI. qed.

  lemma peval_poly_prod_conseq p n x :
    0 <= n =>
    is_fromint (peval p x) =>
    peval (poly_prod_conseq p n) x =
    (BIM.bigi predT ((+) (floor (peval p x))) 0 n)%r.
  proof.
    move=> le0n; case=> y eq_; rewrite eq_ from_int_floor.
    rewrite /poly_prod_conseq; elim: n le0n => [|n le0n IHn].
    + by rewrite range_geq // BIM.big_nil PCM.big_nil peval1.
    rewrite rangeSr // BIM.big_rcons PCM.big_rcons /(predT n) /= pevalM IHn fromintM.
    by congr; rewrite pevalD eq_ pevalC -fromintD.
  qed.

  lemma peval_poly_bin p n x :
    0 <= n =>
    is_fromint (peval p x) =>
    peval (poly_bin p n) x =
    (BIM.bigi predT ((+) (floor (peval p x))) 0 n)%r / (fact n)%r.
  proof.
    move=> le0n is_fromint_; rewrite /poly_bin pevalM.
    by rewrite peval_poly_prod_conseq // pevalC RField.mul1r.
  qed.

  lemma peval_poly_prod_bin n m s x :
    0 <= n =>
    all (fun j => is_fromint (peval (m j) x)) (range 1 (n + 1)) =>
    peval (poly_prod_bin n m s) x =
    BRM.bigi predT
      (fun j => (BIM.bigi predT ((+) (floor (peval (m j) x))) 0 (nth 0 s (j - 1)))%r /
                (fact (nth 0 s (j - 1)))%r )
      1 (n + 1).
  proof.
    move=> le0n is_fromint_; rewrite /poly_prod_bin peval_prod.
    apply/BRM.eq_big_int => j /mem_range mem_j /=.
    rewrite peval_poly_bin //; last first.
    + by move/allP: is_fromint_ => ->.
    (*TODO: permutations lemma.*)
    admit.
  qed.

  op I n q = floor (peval (PI n) q%r).

  lemma eqI n q :
    0 < n =>
    1 < q =>
    BIA.big
      predT
      (fun a =>
        BIM.bigi
          predT
          (fun d => BIM.bigi predT ((+) (I d q)) 0 (nth 0 a (d - 1)) %/ fact (nth 0 a (d - 1)))
          1 (n + 1))
      (allshapes n) =
    q ^ n.
  proof.
    move=> lt0n lt1q; rewrite (BIA.eq_big_perm _ _ _ _ (perm_to_rem (shape n (cc_perm n)) _ _)).
    + (*TODO: permutations lemma.*)
      admit.
    rewrite BIA.big_cons {1}/predT /= eq_sym {1}rangeSr; [by move/ltzE: lt0n|].
    rewrite BIM.big_rcons {1}/predT /= mulrC.
    have ->: nth 0 (shape n (cc_perm n)) (n - 1) = 1.
    + (*TODO: permutations lemma.*)
      admit.
    rewrite BIM.big_int1 fact1 divz1 /= BIM.big1_seq /=.
    + move=> k [_ mem_k] /=.
      have ->: nth 0 (shape n (cc_perm n)) (k - 1) = 0.
      - (*TODO: permutations lemma.*)
        admit.
      by rewrite fact0 // divz1 range_geq // BIM.big_nil.
    rewrite -subr_eq eq_sym; apply/from_int_inj; rewrite fromintB.
    rewrite {1}/I; move/(_ n q)/is_fromintP: PI_int => ->.
    rewrite {1}/PI; move: lt0n; rewrite -(subrK n 1); pose m:= n - 1; move: m => {n} n.
    move/ltzS => le0n; rewrite siterS //= {1}/sPI pevalB pevalXn addr_ge0 //=.
    rewrite RField.fromintXn ?addr_ge0 //=; congr; congr; rewrite peval_sum Bigreal.sumr_ofint.
    apply/Bigreal.BRA.eq_big_seq => p; rewrite rem_filter /=.
    + (*TODO: permutations lemma.*)
      admit.
    rewrite mem_filter /predC1 => -[neqp_ mem_p].
    rewrite peval_poly_prod_bin /=.
    + by apply/addr_ge0.
    + apply/allP => j /= mem_j; rewrite le2_mem_range.
      by pose b:= mem _ _; case: b => _; [rewrite PI_int|rewrite peval1 is_fromint_fromint].
    rewrite prodr_ofint; apply/BRM.eq_big_int => j /mem_range mem_j /=.
    rewrite fromint_div; [|congr; congr].
    + rewrite (BIM.eq_big_seq _ (idfun \o ((+) (I j q)))).
      - by move=> ? _; rewrite /idfun /(\o).
      rewrite -BIM.big_mapT -range_add /=; apply/dvd_fact_prod_range.
      by rewrite -addrA.
    rewrite le2_mem_range range_ltn /=; [by apply/ltzS|].
    move: mem_j; rewrite (rangeSr 1 (n + 1)) /=; [by apply/ler_subl_addr|].
    rewrite mem_rcons /=; case=> [->>|mem_j]; last first.
    + by rewrite mem_j /=; apply/BIM.eq_big_seq => c mem_c; rewrite /I /PI.
    rewrite mem_range /= (gtr_eqF _ 0) /=; [by apply/ltzS|].
    have->: nth 0 p n = 0; [|by rewrite range_geq].
    (*TODO: permutations lemma.*)
    admit.
  qed.

  lemma lt0I n :
    0 < n =>
    exists (q : int) , forall r , q <= r => 0 < I n r.
  proof.
    move=> lt0n; move: (gt0lc_cnvtopi (PI n) _ _).
    + rewrite (eqdeg_PI (n - 1)) /=; [by apply/ltzS|].
      by apply/ltr_subl_addr.
    + rewrite (lc_PI (n - 1)) /=; [by apply/ltzS|].
      by apply/StdOrder.RealOrder.invr_gt0/lt_fromint.
    case/(_ 1%r) => q lt_; exists q => r leqr.
    move/(_ _ leqr): lt_; rewrite /I; pose x:= peval _ _; move=> lt_.
    apply/lt_fromint/(StdOrder.RealOrder.ler_lt_trans _ _ _ _ (floor_gt x)).
    by apply/StdOrder.RealOrder.subr_ge0/StdOrder.RealOrder.ltrW.
  qed.

end Counting_Argument.
