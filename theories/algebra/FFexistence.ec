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

  import SIterOp.
  import PolyReal.
  import PrePolyReal.BigCf.
  import BigPoly.
  import Bigint.

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

  lemma PI_int (n k : int) :
    is_fromint (peval (PI n) k%r).
  proof.
    rewrite/PI; case (n <= 0) => [ltn0|/ltrNge/ltzW].
    + by rewrite siter0 // peval1 is_fromint_fromint.
    elim/sintind: n => n /ler_eqVlt [<<- _|].
    + by rewrite siter0 // peval1 is_fromint_fromint.
    rewrite -(subrK n 1); pose m:= n - 1; move: m => {n} n.
    move/ltzS => le0n IHn; rewrite siterS //= {1}/sPI.
    rewrite pevalB pevalXn peval_sum is_fromintB.
    + by case (0 <= n + 1) => [le_|_]; [apply/is_fromint_exp => //|]; apply/is_fromint_fromint.
    apply/is_fromint_sum/allP => /= r mem_r _; rewrite peval_prod.
    apply/is_fromint_prod/allP => x mem_x _ /=.
    rewrite pevalM peval_prod pevalC /=.
    pose F:=
      idfun \o
      ((+) (floor (peval (if 0 <= x && x <= n then (siter x sPI poly1) else poly1) k%r))).
    rewrite (Bigreal.BRM.eq_big_seq _ (fun y => (F y)%r) _); last first.
    + rewrite -Bigreal.prodr_ofint -fromint_div ?is_fromint_fromint //.
      rewrite -BIM.big_mapT -range_add /= dvd_fact_prod_range.
      by rewrite -addrA -ler_subl_addl.
    move=> i mem_i; rewrite /F /(\o) /idfun /= => {F}.
    rewrite pevalD pevalC fromintD; congr; rewrite eq_sym -is_fromintP.
    rewrite le2_mem_range; move: mem_x; rewrite -(subrK (n + 2) 1).
    rewrite rangeSr /=; [by apply/ler_subl_addr|].
    rewrite mem_rcons /=; case=> [->>|mem_x].
    + by rewrite mem_range /= peval1 is_fromint_fromint.
    rewrite range_ltn ?ltzS //= mem_x /=.
    by rewrite IHn -mem_range; move: mem_x; apply/mem_range_incl.
  qed.

  lemma ledegPI n :
    0 <= n =>
    deg (PI n) <= n + 1.
  proof.
    rewrite/PI; elim/sintind: n => n /ler_eqVlt [<<- _|].
    + by rewrite siter0 // deg1.
    rewrite -(subrK n 1); pose m:= n - 1; move: m => {n} n.
    move/ltzS => le0n IHn; rewrite siterS //= {1}/sPI.
    apply/(ler_trans _ _ _ (degB _ _)); rewrite degXn /= (ler_maxr 0); [by apply/addr_ge0|].
    apply/ler_maxrP => /=; rewrite PCA.big_seq; apply/BigPoly.deg_sum; [by apply/addr_ge0|].
    move=> a; rewrite /= rem_filter.
    + admit.
    move=> /mem_filter; rewrite {1}/predC1 /= => -[neqa /allshapesP /is_shapeP].
    case=> p [is_p_p <<-]; move: neqa; rewrite shape_eq ?is_perm_id //.
    rewrite negb_exists /= => /(_ (id_perm (n + 1))).
    (*TODO: permutations lemmas to simplify this.*)
    rewrite /conj => neq_p_id.
    apply/(ler_trans _ _ _ (BigPoly.deg_prod_le _ _ _)) => /=.
    case: (all _ _) => /=; [apply/ler_subr_addr => /=|by apply/addr_ge0].
    apply/(ler_trans _ _ _ (Bigint.ler_sum_seq _ _ (fun i => i * (nth 0 (shape (n + 1) p) i)) _ _)).
    + move=> k mem_k _; rewrite {1}/(\o) /= -(ler_add2r 2) /=.
      (*TODO: useless and confusing notation. remove abbrev (/name). *)
      print PolyInt.PrePolyInt.IDCoeff.(/).
      apply/(ler_trans _ _ _ (degM_le_or _ _ _)) => /=.
      - by right; rewrite eq_polyC0 RField.invr_eq0 eq_fromint gtr_eqF // fact_gt0.
      rewrite degC RField.invr_eq0 eq_fromint gtr_eqF ?fact_gt0 //=; apply/ler_subr_addr => /=.
      apply/(ler_trans _ _ _ (BigPoly.deg_prod_le _ _ _)) => /=.
      case: (all _ _) => /=; last first.
      - apply/addr_ge0 => //; apply/mulr_ge0; [by move: mem_k; apply/mem_range_le|].
        admit.
      apply/ler_add2r; move: (Bigint.bigi_constz k 0 (nth 0 (shape (n + 1) p) k) _) => /=.
      - admit.
      move=> <-; apply/ler_sum_seq => x mem_x _; rewrite /(\o) /=.
      apply/ler_subl_addr/(ler_trans _ _ _ (degD _ _))/ler_maxrP.
      split; [|by rewrite degC -ler_subl_addr; move: mem_k; apply/mem_range_le; case (_ = _)].
      case: (0 <= k && k <= n) => ?; [by apply/IHn; rewrite ltzS|].
      by rewrite deg1 -ler_subl_addr; move: mem_k; apply/mem_range_le.
    admit.
  qed.

  lemma lcPI n :
    0 <= n =>
    (PI n).[n] = if n = 0 then 1%r else 1%r / n%r.
  proof.
    rewrite/PI; elim/sintind: n => n /ler_eqVlt [<<- _|].
    + by rewrite siter0 // polyCE.
    rewrite -(subrK n 1); pose m:= n - 1; move: m => {n} n.
    move/ltzS => le0n IHn; rewrite siterS //= {1}/sPI.
    rewrite gtr_eqF ?ltzS //= polyDE polyXnE /= addr_ge0 //= polyNE.
    rewrite PrePolyReal.IDCoeff.subr_eq eq_sym BigPoly.polysumE.
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
          (fun d => BIM.bigi predT ((+) (I n q)) 0 (nth 0 a d) %/ fact (nth 0 a d))
          1 (n + 1))
      (allshapes n) =
    q ^ n.
  proof.
    move=> lt0n lt1q; rewrite (BIA.eq_big_perm _ _ _ _ (perm_to_rem (shape n (id_perm n)) _ _)).
    + admit.
    rewrite BIA.big_cons {1}/predT /= eq_sym -subr_eq eq_sym rangeSr; [by move/ltzE: lt0n|].
    rewrite BIM.big_rcons {1}/predT /= mulrC.
    have ->: nth 0 (shape n (id_perm n)) n = 1 by admit.
    rewrite /= rangeS BIM.big_cons BIM.big_nil {1}/predT /= fact1 divz1.
    rewrite BIM.big1_seq /=.
    + move=> k [_ mem_k].
      have ->: nth 0 (shape n (id_perm n)) k = 0 by admit.
      rewrite fact0 // divz1.
      print BigInt.big_geq.
      admit.
    admit.
  qed.

  lemma lt0I n :
    0 < n =>
    exists (q : int) , forall r , q <= r => 0 < I n r.
  proof.
    admit.
  qed.

end Counting_Argument.
