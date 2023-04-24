(* ==================================================================== *)
require import AllCore List Ring Int IntMin IntDiv Real RealExp Poly.
require import StdBigop StdPoly Binomial Counting Perms.
require import RingStruct SubRing PolyDiv FiniteRing Ideal.
(*---*) import StdOrder.IntOrder.


(*TODO: move somewhere else.*)
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
    + by rewrite iteriS // {1}/g ltr_eqF ?ltzS //= IHi // leki /= (ler_trans _ _ _ leki) //;
      apply/ltzW/ltzS.
    rewrite iteriS // {1}/g gtr_eqF //= IHi // !(lerNgt k) lt_k /=.
    by rewrite (ler_lt_trans _ _ _ _ lt_k) //; apply/ltzW/ltzS.
  qed.
end SIterOp.


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
      (rem (shape (cc_perm (range 0 k))) (allshapes k)).

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
    + left => /=; move: mem_s; rewrite rem_filter ?allshapes_uniq // mem_filter.
      rewrite /predC1 => -[] neq_ /allshapesP => is_s_s.
      move: (cc_is_shapeW 0 _ _ is_s_s) => /=.
      move/allP/(_ (nth 0 s n)): (is_shape_ge0 _ _ is_s_s).
      rewrite mem_nth /=; [by rewrite le0n ltzE /= (is_shape_size _ _ is_s_s)|].
      case/ler_eqVlt => [/eq_sym eq_ //|lt_]; rewrite lt_ /= => ->>.
      by move: neq_; rewrite (cc_shapeP (n + 1)) ?ltzS // perm_eq_refl.
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
      move/allP/(_ (nth 0 (shape p) (k - 1))): (shape_ge0 p); rewrite (nth_mem 0) //.
      exists (k - 1) => /=; rewrite -mem_range mem_range_subr size_shape.
      by rewrite (size_is_perm _ _ is_p_p).
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
    case/is_shapeP: is_shape_ => p [is_p_p <<-].
    move/allP/(_ (nth 0 (shape p) (j - 1))): (shape_ge0 p); rewrite (nth_mem 0) //.
    exists (j - 1) => /=; rewrite -mem_range mem_range_subr size_shape.
    by rewrite (size_is_perm _ _ is_p_p).
  qed.

  lemma eqdeg_poly_prod_bin n m s :
    0 <= n =>
    is_shape (n + 1) s =>
    deg (poly_prod_bin (n + 1) m s) =
    if (all (fun j => all (fun c => m j + polyC c%r <> poly0)
            (range 0 (nth 0 s (j - 1)))) (range 1 (n + 2)))
    then BIA.bigi predT (fun j => (nth 0 s (j - 1)) * (deg (m j) - 1)) 1 (n + 2) + 1
    else 0.
  proof.
    move=> le0n is_shape_; rewrite /poly_prod_bin.
    pose b:= (all _ _); case: b; rewrite /b => {b}.
    + move=> /allP all_; rewrite deg_prod /=.
      pose b:= (all _ _); have: b; rewrite /b => {b}.
      - apply/allP => j mem_j; rewrite /predC /predI /predT /=.
        apply/neqpoly0_poly_bin; [|by apply/all_].
        case/is_shapeP: is_shape_ => p [is_p_p <<-].
        move/allP/(_ (nth 0 (shape p) (j - 1))): (shape_ge0 p); rewrite (nth_mem 0) //.
        exists (j - 1) => /=; rewrite -mem_range mem_range_subr size_shape.
        by rewrite (size_is_perm _ _ is_p_p).
      move=> -> /=; congr; apply/BIA.eq_big_seq => j mem_j.
      rewrite /(\o) /= eqdeg_poly_bin; [|by move/(_ _ mem_j): all_ => /= ->].
      case/is_shapeP: is_shape_ => p [is_p_p <<-].
      move/allP/(_ (nth 0 (shape p) (j - 1))): (shape_ge0 p); rewrite (nth_mem 0) //.
      exists (j - 1) => /=; rewrite -mem_range mem_range_subr size_shape.
      by rewrite (size_is_perm _ _ is_p_p).
    rewrite -has_predC => /hasP [j] [mem_j]; rewrite /predC /=.
    rewrite -has_predC => /hasP [c] [mem_c]; rewrite /predC /= => eq_.
    apply/deg_eq0/BigPoly.prodr_eq0; exists j; rewrite /predT mem_j /=.
    apply/deg_eq0; rewrite eqdeg_poly_bin; last first.
    + pose b:= all _ _; have: !b; rewrite /b => {b}; [|by move=> ->].
      by rewrite -has_predC; apply/hasP; exists c; split.
    case/is_shapeP: is_shape_ => p [is_p_p <<-].
    move/allP/(_ (nth 0 (shape p) (j - 1))): (shape_ge0 p); rewrite (nth_mem 0) //.
    exists (j - 1) => /=; rewrite -mem_range mem_range_subr size_shape.
    by rewrite (size_is_perm _ _ is_p_p).
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
          by rewrite degDl deg_ ?degC -ltr_subl_addr;
          move: mem_j; apply/mem_range_lt => //; case (_ = _).
        rewrite all_ /= -subr_eq0 addrAC opprD !addrA /= -addrA -opprD subr_eq0.
        rewrite -(is_shape_sum 0 _ _ is_s_s) /=.
        apply/BIA.eq_big_seq => j mem_j /=; rewrite le2_mem_range mulrC.
        rewrite range_ltn /=; [by apply/ltzS|]; move: mem_j.
        rewrite (rangeSr _ (n + 1)); [by apply/ler_subl_addr|].
        rewrite mem_rcons /=; case=> [->>|mem_j]; last first.
        * by rewrite mem_j /=; case/(_ _ mem_j): IHn => _ [_ ->].
        rewrite /= mem_range /= (gtr_eqF _ 0) /=; [by apply/ltzS|].
        rewrite deg1 /= eq_sym mulrI_eq0; [by apply/lregP/gtr_eqF/ltzS|].
        move: (cc_is_shapeW 0 _ _ is_s_s) => /=.
        move/allP/(_ (nth 0 s n)): (is_shape_ge0 _ _ is_s_s).
        rewrite mem_nth /=; [by rewrite le0n ltzE /= (is_shape_size _ _ is_s_s)|].
        case/ler_eqVlt => [/eq_sym eq_ //|lt_]; rewrite lt_ /= => ->>.
        by move: neqs_; rewrite (cc_shapeP (n + 1)) ?ltzS // perm_eq_refl.
      rewrite lc_poly_prod_bin //.
      - move=> j mem_j /=; rewrite le2_mem_range.
        rewrite range_ltn /=; [by apply/ltzS|]; move: mem_j.
        rewrite (rangeSr _ (n + 1)); [by apply/ler_subl_addr|].
        rewrite mem_rcons /=; case=> [->>/=|mem_j]; last first.
        * rewrite mem_j /=; case/(_ _ mem_j): IHn => _ [_ ->].
          by rewrite -ltr_subl_addr; right; move: mem_j; apply/mem_range_lt.
        rewrite mem_range /= (gtr_eqF (_ + 1) 0) /=; [by apply/ltzS|].
        rewrite deg1 /=; move: (cc_is_shapeW 0 _ _ is_s_s) => /=.
        move/allP/(_ (nth 0 s n)): (is_shape_ge0 _ _ is_s_s).
        rewrite mem_nth /=; [by rewrite le0n ltzE /= (is_shape_size _ _ is_s_s)|].
        case/ler_eqVlt => [/eq_sym eq_ //|lt_]; rewrite lt_ /= => ->>.
        by move: neqs_; rewrite (cc_shapeP (n + 1)) ?ltzS // perm_eq_refl.
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
        case/is_shapeP: is_s_s => p [is_p_p <<-].
        move/allP/(_ (nth 0 (shape p) (j - 1))): (shape_ge0 p); rewrite (nth_mem 0) //.
        exists (j - 1) => /=; rewrite -mem_range mem_range_subr size_shape.
        rewrite (size_is_perm _ _ is_p_p); move: mem_j; apply/mem_range_incl => //.
        by apply/ltzW/ltzE.
      rewrite mem_range /= (gtr_eqF (_ + 1) 0) /=; [by apply/ltzS|].
      rewrite lc1 /= RField.expr1z RField.mul1r fromintM RField.invfM.
      apply/(RField.mulrI (fact (nth 0 s n))%r).
      - by rewrite eq_fromint; apply/gtr_eqF/fact_gt0.
      rewrite RField.mulrA RField.mulrAC RField.divff.
      - by rewrite eq_fromint; apply/gtr_eqF/fact_gt0.
      rewrite RField.mul1r eq_sym RField.invr_eq1.
      move: (cc_is_shapeW 0 _ _ is_s_s) => /=.
      move/allP/(_ (nth 0 s n)): (is_shape_ge0 _ _ is_s_s).
      rewrite mem_nth /=; [by rewrite le0n ltzE /= (is_shape_size _ _ is_s_s)|].
      case/ler_eqVlt => [/eq_sym eq_ //|lt_]; [by rewrite eq_ expr0|].
      by rewrite lt_ /= => ->>; move: neqs_; rewrite (cc_shapeP (n + 1)) ?ltzS // perm_eq_refl.
    rewrite Bigreal.BRA.big_filter.
    rewrite (Bigreal.BRA.eq_bigl _ (predC (pred1 (shape (cc_perm (range 0 (n + 1))))))).
    + by move=> ?; rewrite /predC1 /predC /pred1.
    rewrite -RField.subr_eq0 -RField.addrA -RField.opprD RField.subr_eq0 eq_sym RField.addrC.
    pose P:= pred1 _; pose s:= allshapes _.
    pose f:= (fun s =>
               Bigreal.BRM.bigi _
                 (fun j => (_ / (j ^ _ _ s (j - 1) * _ (_ _ s (j - 1)))%r)) _ _).
    move: (Bigreal.BRA.bigEM P f s); have ->: Bigreal.BRA.big P f s = inv (n + 1)%r.
    + rewrite -Bigreal.BRA.big_filter /P => {P}; rewrite filter_pred1 count_uniq_mem /s => {s}.
      - by apply/allshapes_uniq.
      pose b:=(_ \in _); have: b; rewrite /b => {b} [|->].
      - rewrite -allshapesP is_shapeP; exists (cc_perm (range 0 (n + 1))) => /=.
        by apply/is_perm_cc; [apply/ltzS|apply/perm_eq_refl].        
      rewrite b2i1 nseq1 Bigreal.BRA.big_seq1 /f => {f}.
      rewrite (cc_shapeP (n + 1)) /=; [by apply/ltzS|by apply/perm_eq_refl|].
      rewrite (rangeSr 1 (n + 1)); [by apply/subr_ge0|].
      rewrite BRM.big_rcons /(predT (n + 1)) /= nth_rcons size_nseq ler_maxr //=.
      rewrite expr1 fact1 /= BRM.big1_seq //= => i [] _ memi.
      rewrite nth_rcons size_nseq ler_maxr // ltr_subl_addr nth_nseq.
      - by apply/mem_range/mem_range_subr.
      by case/mem_range: memi => _ -> /=; rewrite expr0 fact0.
    move=> <-; rewrite /P /f /s => {P f s}.
    apply/(RField.mulfI (fact (n + 1))%r).
    + by rewrite eq_fromint gtr_eqF // fact_gt0.
    rewrite RField.mulr1 BRA.mulr_sumr -{2}size_sum_allshapes sumr_ofint.
    apply/BRA.eq_big_seq => s /allshapesP is_s_s; rewrite /(\o) /=.
    rewrite -(size_allperms_shape 0 _ _ is_s_s) fromintM -RField.mulrA.
    rewrite -{2}(RField.mulr1 (size _)%r); congr.
    rewrite (range_addr 1 (n + 1) 1) BRM.big_mapT /=.
    rewrite prodr_ofint -BRM.big_split; apply/BRM.big1_seq.
    move=> i [] _ memi; rewrite /(\o) /= (addrC 1) RField.divrr //.
    rewrite eq_fromint; apply/gtr_eqF/mulr_gt0; [|by apply/fact_gt0].
    by apply/expr_gt0/ltzS; move: memi; apply/mem_range_le.
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
    is_shape n s =>
    all (fun j => is_fromint (peval (m j) x)) (range 1 (n + 1)) =>
    peval (poly_prod_bin n m s) x =
    BRM.bigi predT
      (fun j => (BIM.bigi predT ((+) (floor (peval (m j) x))) 0 (nth 0 s (j - 1)))%r /
                (fact (nth 0 s (j - 1)))%r )
      1 (n + 1).
  proof.
    move=> le0n is_s_s is_fromint_; rewrite /poly_prod_bin peval_prod.
    apply/BRM.eq_big_int => j /mem_range mem_j /=.
    rewrite peval_poly_bin //; last first.
    + by move/allP: is_fromint_ => ->.
    case/is_shapeP: is_s_s => p [is_p_p <<-].
    move/allP/(_ (nth 0 (shape p) (j - 1))): (shape_ge0 p); rewrite (nth_mem 0) //.
    exists (j - 1) => /=; rewrite -mem_range mem_range_subr size_shape.
    by rewrite (size_is_perm _ _ is_p_p).
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
    move=> lt0n lt1q.
    rewrite (BIA.eq_big_perm _ _ _ _ (perm_to_rem (shape (cc_perm (range 0 n))) _ _)).
    + apply/allshapesP/is_shapeP; exists (cc_perm (range 0 n)) => /=.
      by apply/is_perm_cc => //; apply/perm_eq_refl.
    rewrite BIA.big_cons {1}/predT /= eq_sym {1}rangeSr; [by move/ltzE: lt0n|].
    rewrite BIM.big_rcons {1}/predT /= mulrC (cc_shapeP n) //; [by apply/perm_eq_refl|].
    rewrite nth_rcons size_nseq ler_maxr -?ltzS //= fact1 /= range_ltn // range_geq //=.
    rewrite BIM.big_seq1 /= BIM.big1_seq /= => [i [] _ memi|].
    + rewrite nth_rcons size_nseq ler_maxr -?ltzS // ltr_subl_addr /= nth_nseq.
      - by apply/mem_range/mem_range_subr.
      by case/mem_range: memi => _ -> /=; rewrite range_geq // fact0.
    rewrite -subr_eq eq_sym; apply/from_int_inj; rewrite fromintB.
    rewrite {1}/I; move/(_ n q)/is_fromintP: PI_int => ->.
    rewrite {1}/PI; move: lt0n; rewrite -(subrK n 1); pose m:= n - 1; move: m => {n} n.
    move/ltzS => le0n; rewrite siterS //= {1}/sPI pevalB pevalXn addr_ge0 //=.
    rewrite RField.fromintXn ?addr_ge0 //=; congr; congr; rewrite peval_sum.
    rewrite Bigreal.sumr_ofint (cc_shapeP (n + 1)) /=; [by apply/ltzS|by apply/perm_eq_refl|].
    apply/Bigreal.BRA.eq_big_seq => s; rewrite rem_filter /=.
    + by apply/allshapes_uniq.
    rewrite mem_filter /predC1 => -[] neqp_ /allshapesP is_s_s.
    rewrite peval_poly_prod_bin //=; [by apply/addr_ge0| |].
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
    move: (cc_is_shapeW 0 _ _ is_s_s); rewrite neqp_ /=.
    move/is_shape_ge0/allP/(_ (nth 0 s n)): (is_s_s).
    rewrite mem_nth ?(is_shape_size _ _ is_s_s) ?ltzS //=.
    by case/ler_eqVlt => // <- /=; rewrite range_geq.
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


abstract theory PolyFiniteField.
  type t.

  clone import Field as RL with
    type t <= t.

  clone import Idomain as PID with
    type coeff <= t,
    theory IDC <= RL.

  clone include FiniteRing.FiniteField with
    type t    <- t,
    theory RL <- RL
    (*, theory IDStr.FrobeniusPoly.Po <= PID.P*)
    rename [theory] "RL" as "Gone".

  clone import Ideal as IdealP with
    type t             <= PID.poly,
    theory IDomain     <= P.IDPoly,
    theory BigDom.BAdd <= P.BigPoly.PCA,
    theory BigDom.BMul <= P.BigPoly.PCM.

  import P.
  import BigPoly.

  lemma scaled_monicP p :
    scaled_monic p <=> p <> poly0.
  proof.
    split=> [[c r] [] neqc0 [] m_ ->>|neqp0].
    + by rewrite -scaler_eq0 negb_or neqc0 -lc_eq0 m_ RL.oner_neq0.
    exists (lc p) ((RL.invr (lc p)) ** p).
    rewrite lc_eq0 neqp0 /= monic_invrZ ?RL.unitfP ?lc_eq0 //=.
    by rewrite scalepA RL.mulrV ?scale1r // RL.unitfP lc_eq0.
  qed.

  op enum_ledeg n =
    if 0 <= n
    then map polyL (alltuples n FT.enum)
    else [].

  op enum_deg n = filter (fun p => deg p = n) (enum_ledeg n).

  op enum_udeg n = filter monic (enum_deg n).

  op enum_udeg_irr_shape n s =
    filter
      ( fun p =>
          exists qs ,
            irreducible_monic_dec p qs /\
            s = mkseq (fun k => count (fun q => deg q = k + 2) qs) (n - 1) )
      (enum_udeg n).

  op enum_udeg_irr_deg k d =
    filter
      ( fun p =>
          exists qs ,
            irreducible_monic_dec p qs /\
            size qs = k /\
            all (fun q => deg q = d) qs )
      (enum_udeg (k * (d - 1) + 1)).

  op enum_iudeg n = filter irreducible_poly (enum_udeg n).

  lemma enum_ledegP n p :
    p \in enum_ledeg n <=>
    (P.deg p <= n).
  proof.
    rewrite /enum_ledeg; case (0 <= n) => [le0n|/ltrNge ltn0]; last first.
    + by rewrite lerNgt (ltr_le_trans _ _ _ ltn0 (ge0_deg p)).
    rewrite mapP; split=> [[cs]|le_].
    + rewrite alltuplesP => -[] [] eq_ _ ->>.
      by apply/(ler_trans _ _ _ (degL_le _)); rewrite eq_ ler_maxrP.
    case: (surj_polyL _ _ le_) => s [] eq_ ->>; exists s.
    rewrite alltuplesP eq_ ler_maxr //=.
    by apply/allP => ? _; apply/FT.enumP.
  qed.

  lemma uniq_enum_ledeg n :
    uniq (enum_ledeg n).
  proof.
    rewrite /enum_ledeg; case (0 <= n) => // le0n.
    apply/map_inj_in_uniq; [|by apply/alltuples_uniq/FT.enum_uniq].
    move=> xs ys /alltuplesP [] + _ /alltuplesP [] + _.
    by rewrite ler_maxr // => <<- /eq_sym; apply/inj_polyL.
  qed.

  lemma size_enum_ledeg n :
    0 <= n =>
    size (enum_ledeg n) = FT.card ^ n.
  proof.
    move=> le0n; rewrite /enum_ledeg le0n /= size_map.
    by rewrite size_alltuples ler_maxr.
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
    size (enum_deg n) = (FT.card - 1) * FT.card ^ (n - 1).
  proof.
    move=> lt0n; rewrite /card_deg.
    move/perm_eq_size: (perm_eq_enum_deg n).
    rewrite size_cat !size_enum_ledeg; [by apply/ltzW|by apply/ltzS|].
    rewrite (IntID.addrC _ (size _)) -subr_eq => <-.
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
      case/ler_eqVlt => [<<-/=|lt_]; [by rewrite RL.subr_eq0 -eq_p up|].
      rewrite gtr_eqF //= RL.subr0; apply/P.gedeg_coeff; rewrite eq_p.
      by move/ltzE: lt_.
    case=> q [/enum_ledegP le_ ->>]; rewrite /monic degDl.
    + by rewrite degXn ler_maxr //=; [apply/ltzW|move/ltzS: le_].
    rewrite degXn /= ler_maxr; [by apply/ltzW|].
    rewrite polyDE polyXnE /= -ltzS lt0n /= RL.addrC -RL.subr_eq0.
    by rewrite -RL.addrA RL.subrr RL.addr0; apply/P.gedeg_coeff.
  qed.

  lemma size_enum_udeg n :
    0 < n =>
    size (enum_udeg n) = FT.card ^ (n - 1).
  proof.
    move=> lt0n; rewrite /card_udeg.
    move/perm_eq_size: (perm_eq_enum_udeg _ lt0n) => ->.
    by rewrite size_map size_enum_ledeg // -ltzS.
  qed.

  lemma enum_udeg_irr_shapeP n s p :
    p \in enum_udeg_irr_shape n s <=>
    ( monic p /\
      deg p = n /\
      exists qs ,
        irreducible_monic_dec p qs /\
        s = mkseq (fun k => count (fun q => deg q = k + 2) qs) (n - 1) ).
  proof.
    rewrite /enum_udeg_irr_shape mem_filter enum_udegP /=.
    by split=> />.
  qed.

  lemma uniq_enum_udeg_irr_shape n s :
    uniq (enum_udeg_irr_shape n s).
  proof. by rewrite filter_uniq; apply/uniq_enum_udeg. qed.

  lemma perm_eq_enum_udeg_irr_shape n :
    1 < n =>
    perm_eq (enum_udeg n) (flatten (map (enum_udeg_irr_shape n) (allshapes (n - 1)))).
  proof.
    move=> lt1n; apply/uniq_perm_eq.
    + by apply/uniq_enum_udeg.
    + apply/uniq_flatten_map; last first.
      - by apply/allshapes_uniq.
      - by move=> ?; apply/uniq_enum_udeg_irr_shape.
      move=> p1 p2 mem1 mem2 /hasP [p] [].
      case/enum_udeg_irr_shapeP => m_ [] eq_ [qs2] [] dec2 ->>.
      case/enum_udeg_irr_shapeP => _ [] _ [qs1] [] dec1 ->>.
      apply/eq_in_mkseq => i /mem_range mem_ /=.
      by apply/perm_eqP/(irredp_monic_dec_perm_eq p).
    move=> p; rewrite enum_udegP -flattenP; split; last first.
    + case=> ? [] /mapP [s] [] /allshapesP is_s_ ->>.
      by case/enum_udeg_irr_shapeP => m_ [] <<- [?] [] dec_ ->>.
    case=> m_ <<-; move: (irredp_monic_decW p).
    rewrite scaled_monicP -deg_gt0 ltzE ltzW //= => -[qs] dec_.
    pose s:= mkseq (fun k => count (fun q => deg q = k + 2) qs) (deg p - 1).
    pose ps:= enum_udeg_irr_shape (deg p) s; exists ps; split; last first.
    + rewrite /ps => {ps}; apply/enum_udeg_irr_shapeP; rewrite m_ /=.
      by exists qs; rewrite -/s.
    apply/mapP; exists s; rewrite -/ps /= => {ps}; apply/allshapesP.
    apply/is_shapeW.
    + by rewrite size_mkseq ler_maxr // -ltzS /= ltzE ltzW.
    + rewrite all_map range_iota /preim /=; apply/allP.
      by move=> i memi /=; apply/count_ge0.
    move=> dflt /=.
    rewrite (Bigint.BIA.eq_big_seq _ (fun k => k * count (fun q => deg q = k + 1) qs)).
    + by move=> k memk /=; rewrite nth_mkseq // -mem_range mem_range_subr.
    rewrite eq_sym {1}(deg_irredp_monic_dec _ _ dec_) /=.
    rewrite (Bigint.big_mcount _ _ 1 (deg p)).
    + move=> ? /mapP [] q [] memq ->>; apply/mem_range_subr.
      by rewrite /=; move: (degs_irredp_monic_dec _ _ _ dec_ memq).
    apply/Bigint.BIA.eq_big_seq => i memi /=; rewrite count_map /preim /pred1 /=.
    by congr; apply/eq_count => q /=; split=> [<-|->].
  qed.

  lemma size_enum_udeg_irr_shape n :
    1 < n =>
    Bigint.BIA.big predT (fun s => size (enum_udeg_irr_shape n s)) (allshapes (n - 1)) =
    FT.card ^ (n - 1).
  proof.
    move=> lt1n; rewrite -size_enum_udeg ?ltzE ?ltzW //.
    move/perm_eq_size: (perm_eq_enum_udeg_irr_shape _ lt1n) => ->.
    rewrite size_flatten Bigint.sumzE !Bigint.BIA.big_mapT.
    apply/Bigint.BIA.eq_big_seq => s mem_ /=.
    by rewrite /(\o).
  qed.

  lemma enum_udeg_irr_degP k d p :
    p \in enum_udeg_irr_deg k d <=>
    ( monic p /\
      exists qs ,
        irreducible_monic_dec p qs /\
        size qs = k /\
        all (fun q => deg q = d) qs ).
  proof.
    rewrite /enum_iudeg mem_filter enum_udegP /=.
    split=> |> m_ qs dec_ all_; rewrite (deg_irredp_monic_dec _ _ dec_).
    rewrite (Bigint.BIA.eq_big_seq _ (fun _ => d - 1)) /=.
    + by move=> q mem_; move/allP/(_ _ mem_): all_ => ->.
    by rewrite Bigint.BIA.sumr_const intmulz mulrC count_predT.
  qed.

  lemma uniq_enum_udeg_irr_deg k d :
    uniq (enum_udeg_irr_deg k d).
  proof. by rewrite filter_uniq; apply/uniq_enum_udeg. qed.

  lemma perm_eq_enum_udeg_irr_deg n s :
    1 < n =>
    is_shape (n - 1) s =>
    perm_eq
      (enum_udeg_irr_shape n s)
      (map (PCM.big predT idfun)
           (alltuples_list (mapi ((transpose enum_udeg_irr_deg) \o (transpose Int.(+) 2)) s))).
  proof.
    move=> lt1n is_s_s; apply/uniq_perm_eq; [by apply/uniq_enum_udeg_irr_shape| |].
    + rewrite map_inj_in_uniq; last first.
      - apply/alltuples_list_uniq/allP => qs /(mapiP 0) [i] [] /mem_range mem_ ->>.
        by rewrite /(\o) /=; apply/uniq_enum_udeg_irr_deg.
      move=> qs1 qs2 /alltuples_listP [] + all1 /alltuples_listP [] + all2.
      rewrite !size_mapi => size1 size2 eq_; apply/(eq_from_nth witness).
      - by rewrite size1 size2.
      move=> i /mem_range; rewrite size1 => memi.
      pose p:= PCM.big predT idfun qs1; move: (eq_refl p); rewrite {2}/p.
      move: p => p eq1; move: eq_; rewrite -eq1 => eq2.
      move: (partial_funchoice
               (mem (range 0 (size s)))
               (fun j rs => monic (nth witness qs1 j) /\
                            irreducible_monic_dec (nth witness qs1 j) rs /\
                            all (fun q => deg q = j + 2) rs)
               _).
      - move=> j memj; move/allP: all1.
        move/(_ (nth witness qs1 j, enum_udeg_irr_deg (nth witness s j) (j + 2)) _).
        * apply/(nth_mem (witness, witness)); exists j.
          rewrite size_zip size_mapi size1 ler_minr // -mem_range memj /=.
          by rewrite nth_zip ?size_mapi // (nth_mapi witness) //= -mem_range.
        rewrite /= => /enum_udeg_irr_degP [] m_ [rs] [] dec_ [] index_ all_.
        by exists rs.
      case=> f1 f1P; pose qqs1:= map f1 (range 0 (size s)).
      move: (partial_funchoice
               (mem (range 0 (size s)))
               (fun j rs => monic (nth witness qs2 j) /\
                            irreducible_monic_dec (nth witness qs2 j) rs /\
                            all (fun q => deg q = j + 2) rs)
               _).
      - move=> j memj; move/allP: all2.
        move/(_ (nth witness qs2 j, enum_udeg_irr_deg (nth witness s j) (j + 2)) _).
        * apply/(nth_mem (witness, witness)); exists j.
          rewrite size_zip size_mapi size2 ler_minr // -mem_range memj /=.
          by rewrite nth_zip ?size_mapi // (nth_mapi witness) //= -mem_range.
        rewrite /= => /enum_udeg_irr_degP [] m_ [rs] [] dec_ [] index_ all_.
        by exists rs.
      case=> f2 f2P; pose qqs2:= map f2 (range 0 (size s)).
      have dec1: irreducible_monic_dec p (flatten qqs1).
      - apply/irredp_monic_dec_flatten; exists qs1.
        rewrite size1 size_map size_range ler_maxr //= -eq1 eqpxx /=.
        apply/(all_nthP _ _ (witness, witness)) => j /mem_range.
        rewrite size_zip size1 size_map size_range ler_maxr // ler_minr //=.
        move=> memj; rewrite nth_zip ?size1 ?size_map ?size_range ?ler_maxr //=.
        rewrite (nth_map witness) -?mem_range ?size_range ?ler_maxr //.
        rewrite nth_range -?mem_range ?size_range ?ler_maxr //=.
        by move/(_ _ memj): f1P.
      have dec2: irreducible_monic_dec p (flatten qqs2).
      - apply/irredp_monic_dec_flatten; exists qs2.
        rewrite size2 size_map size_range ler_maxr //= -eq2 eqpxx /=.
        apply/(all_nthP _ _ (witness, witness)) => j /mem_range.
        rewrite size_zip size2 size_map size_range ler_maxr // ler_minr //=.
        move=> memj; rewrite nth_zip ?size1 ?size_map ?size_range ?ler_maxr //=.
        rewrite (nth_map witness) -?mem_range ?size_range ?ler_maxr //.
        rewrite nth_range -?mem_range ?size_range ?ler_maxr //=.
        by move/(_ _ memj): f2P.
      move: (irredp_monic_dec_perm_eq _ _ _ dec1 dec2) => eq_.
      move: (flatten_perm_eq deg (range 2 (size s + 2)) _ _ _ _ _ _ _ eq_).
      - by apply/range_uniq.
      - by rewrite size_map !size_range.
      - by rewrite size_map !size_range.
      - apply/(all_nthP _ _ (witness, witness)) => j /mem_range.
        rewrite size_zip size_map !size_range !ler_maxr // ler_minr //= => memj.
        rewrite nth_zip ?size_map ?size_range ?size1 ?ler_maxr //.
        rewrite (nth_map witness) -?mem_range ?size_range ?ler_maxr //.
        rewrite nth_range -?mem_range //=; case/(_ j _): f1P => //= _ [] _.
        by rewrite nth_range -?mem_range //; apply/all_imp_in/allP => q _ /= ->; ring.
      - apply/(all_nthP _ _ (witness, witness)) => j /mem_range.
        rewrite size_zip size_map !size_range !ler_maxr // ler_minr //= => memj.
        rewrite nth_zip ?size_map ?size_range ?size1 ?ler_maxr //.
        rewrite (nth_map witness) -?mem_range ?size_range ?ler_maxr //.
        rewrite nth_range -?mem_range //=; case/(_ j _): f2P => //= _ [] _.
        by rewrite nth_range -?mem_range //; apply/all_imp_in/allP => q _ /= ->; ring.
      move/(all_nthP _ _ (witness, witness))/(_ i); rewrite -mem_range.
      rewrite size_zip !size_map !size_range ler_maxr // ler_minr // memi /=.
      rewrite nth_zip ?size_map //= !(nth_map witness) -?mem_range ?size_range ?ler_maxr //.
      rewrite !nth_range -?mem_range //=.
      case/(_ _ memi): f1P => m1 [] /irredp_monic_decP [] _ [] _ -> _.
      case/(_ _ memi): f2P => m2 [] /irredp_monic_decP [] _ [] _ -> _.
      by rewrite m1 m2 !scale1r; apply/PCM.eq_big_perm.
    move=> p; rewrite enum_udeg_irr_shapeP mapP; split=> [[] m_ [] <<- [qs] [] dec_ ->>|].
    + pose bqs:= mkseq (fun k => PCM.big (fun q => deg q = k + 2) idfun qs) (deg p - 1).
      exists bqs; rewrite alltuples_listP size_mapi !size_mkseq /(\o) /=; split.
      - apply/(all_nthP _ _ (witness, witness)) => i; rewrite size_zip size_mapi !size_mkseq.
        rewrite -mem_range ler_maxr -?ltzS ?ltzE ?ltzW // ler_minr //= => memi.
        rewrite nth_zip /=; [by rewrite size_mapi !size_mkseq|].
        rewrite nth_mkseq -?mem_range //= (nth_mapi witness) /=.
        * by rewrite -mem_range size_mkseq ler_maxr // -ltzS ltzE ltzW.
        apply/enum_udeg_irr_degP; rewrite monic_prod /=.
        * case/irredp_monic_decP: dec_ => + _.
          by apply/all_imp_in/allP => q mem_ /= []; rewrite /idfun.
        rewrite nth_mkseq -?mem_range //=; exists (filter (fun q => deg q = i + 2) qs).
        rewrite size_filter filter_all /=; apply/irredp_monic_decP.
        case/irredp_monic_decP: dec_ => all_ _; rewrite -prodf_neq0.
        rewrite lc_prod PCM.big_filter BigCf.BCM.big1_seq ?scale1r /=.
        * move=> q [] _ mem_; rewrite /(\o) /idfun /=.
          by case/allP/(_ _ mem_): all_.
        rewrite all_filter -all_predI; move: all_; apply/all_imp_in/allP => q mem_.
        rewrite /predA /predI /predC /idfun /= negb_and -implyNb /=.
        by case=> irr_ mq; split=> _ //; apply/irredp_neq0.
      case/irredp_monic_decP: (dec_) => _ [] _ ->; rewrite m_ scale1r.
      rewrite (PCM.partition_big deg _ predT _ _ (range 2 (deg p + 1))).
      - by apply/range_uniq.
      - by move=> q; rewrite /predT /=; apply/degs_irredp_monic_dec.
      rewrite PCM.big_mapT range_iota /= (range_addr 2 (deg p - 1) 2) /=.
      rewrite PCM.big_mapT; apply/PCM.eq_big_seq => i memi.
      by rewrite /(\o) /idfun /=; apply/PCM.eq_big => //; move=> q; rewrite /predT /= addrC.
    case=> qs [] /alltuples_listP []; rewrite size_mapi => size_ all_ ->>.
    rewrite monic_prod /=; [apply/(all_nthP _ _ witness) => i /mem_range /= + _|].
    + move=> memi; move/(all_nthP _ _ (witness, witness))/(_ i): all_.
      rewrite -mem_range size_zip size_mapi -size_ ler_minr // memi /=.
      rewrite nth_zip ?size_mapi //= (nth_mapi witness) -?mem_range -?size_ //.
      by rewrite /(\o) /idfun /= => /enum_udeg_irr_degP.
    move: (partial_funchoice
            (mem (range 0 (n - 1)))
            (fun i rs =>
              monic (nth witness qs i) /\
              irreducible_monic_dec (nth witness qs i) rs /\
              size rs = nth witness s i /\
              all (fun r => deg r = i + 2) rs)
            _).
    + move=> i memi /=; move/(all_nthP _ _ (witness, witness))/(_ i): all_.
      rewrite size_zip size_mapi size_ ler_minr // -mem_range (is_shape_size _ _ is_s_s) memi /=.
      rewrite nth_zip ?size_mapi //=.
      rewrite (nth_mapi witness) -?mem_range ?(is_shape_size _ _ is_s_s) //.
      by rewrite /(\o) /= => /enum_udeg_irr_degP [] ? [rs] ?; exists rs.
    case=> f /= {all_} forall_.
    have ->: qs = map (fun i => PCM.big predT idfun (f i)) (range 0 (n - 1)).
    + apply/(eq_from_nth witness).
      - rewrite size_map size_range size_ (is_shape_size _ _ is_s_s).
        by rewrite ler_maxr //= -ltzS ltzE ltzW.
      move=> i /mem_range; rewrite size_ (is_shape_size _ _ is_s_s) => memi.
      rewrite (nth_map witness) ?size_range -?mem_range ?ler_maxr // -?ltzS ?ltzE ?ltzW //=.
      rewrite nth_range -?mem_range //=; case/(_ _ memi): forall_ => m_ [] dec_ _.
      by case/irredp_monic_decP: dec_ => _ [] _ ->; rewrite m_ scale1r.
    rewrite PCM.big_mapT deg_prod; pose b:= all _ _; have ->: b; rewrite /b => {b} /=.
    + apply/allP => i memi; rewrite /predI /predC /(predT i) /(\o) /(idfun (PCM.big _ _ _)) /=.
      case/(_ _ memi): forall_ => _ [] /irredp_monic_decP [] all_ _ _.
      apply/prodf_neq0; move: all_; apply/all_imp_in/allP => r memr /=.
      rewrite /predI /predC /predT /idfun /= => -[] _.
      by rewrite -lc_eq0 => ->; apply/RL.oner_neq0.
    split; [rewrite eq_sym -subr_eq -{1}(is_shape_sum witness _ _ is_s_s) /=|].
    + move: (range_addr 1 (n - 1) 1) => /= ->; rewrite Bigint.BIA.big_map /=.
      rewrite (Bigint.BIA.eq_bigl _ predT); [by move=> ?; rewrite /(\o) /predT|].
      apply/Bigint.BIA.eq_big_seq => i memi; rewrite /(\o) /idfun /=.
      case/(_ _ memi): forall_ => m_ [] dec_ [] eq_ all_.
      rewrite deg_prod; pose b:= all _ _; have ->: b; rewrite /b => {b} /=.
      - apply/allP => r memr; rewrite /predI /predC /predT /=.
        case/irredp_monic_decP: dec_ => /allP /(_ _ memr) [] _ + _.
        by rewrite -lc_eq0 => ->; apply/RL.oner_neq0.
      rewrite -eq_ (IntID.addrC 1).
      rewrite (Bigint.BIA.eq_big_seq _ (fun _ => i + 1)) ?Bigint.big_constz ?count_predT //.
      by move=> r memr; rewrite /(\o) /=; move/allP/(_ _ memr): all_ => ->.
    exists (flatten (map f (range 0 (n - 1)))); rewrite irredp_monic_decP; do!split.
    + apply/allP => r /flattenP [?] [] /mapP [i] [] memi ->> memr; case/(_ _ memi): forall_.
      by move=> _ [] /irredp_monic_decP [] /allP /(_ _ memr).
    + apply/prodf_neq0/allP => i memi; rewrite /predI /predC /predT /(\o) /idfun /=.
      apply/prodf_neq0/allP => r memr; rewrite /predI /predC /=.
      case/(_ _ memi): forall_ => _ [] /irredp_monic_decP [] /allP /(_ _ memr) [] _ + _ _.
      by rewrite -lc_eq0 => ->; rewrite RL.oner_neq0.
    + rewrite lc_prod (BigCf.BCM.eq_big_seq _ (fun _ => RL.oner)); last first.
      - rewrite BigCf.BCM.big1_eq scale1r PCM.big_flatten PCM.big_map.
        by apply/PCM.eq_big_seq => i memi; rewrite /(\o) /idfun.
      move=> i memi; rewrite /(\o) /idfun /= lc_prod (BigCf.BCM.eq_big_seq _ (fun _ => RL.oner)).
      - move=> r memr; rewrite /(\o) /=; case/(_ _ memi): forall_ => _ [] /irredp_monic_decP.
        by case=> /allP /(_ _ memr) [] _ ->.
      by rewrite BigCf.BCM.big1_eq.
    apply/(eq_from_nth witness) => [|i /mem_range]; rewrite (is_shape_size _ _ is_s_s).
    + by rewrite size_mkseq ler_maxr // -ltzS ltzE ltzW.
    move=> memi; rewrite nth_mkseq -?mem_range //= count_flatten Bigint.sumzE.
    rewrite !Bigint.BIA.big_mapT (Bigint.BIA.big_rem _ _ _ _ memi) /(predT i) /(\o) /=.
    rewrite rem_filter ?range_uniq //Bigint.BIA.big_filter Bigint.BIA.big1_seq /=.
    + move=> j []; rewrite /predC1 eq_sym => neqij memj.
      case/(_ _ memj): forall_ => _ [] _ [] _ all_.
      apply/count_pred0_eq_in => r memr /=.
      move/allP/(_ _ memr): all_ => /= ->.
      by rewrite eq_sym; move: neqij; apply/implybNN/IntID.addIr.
    by case/(_ _ memi): forall_ => _ [] _ [] <-; rewrite eq_sym => /all_count_in ->.
  qed.

  lemma size_enum_udeg_irr_deg n :
    0 < n =>
    Bigint.BIA.big predT
      (fun s => Bigint.BIM.bigi predT
                  (fun i => size (enum_udeg_irr_deg (nth 0 s i) (i + 2)))
                  0 n)
      (allshapes n) =
    FT.card ^ n.
  proof.
    rewrite -(IntID.subrK n (-1)); pose m:= n - - 1; move: m => {n} n /ltzE /ltzS /=.
    move=> lt1n; rewrite -size_enum_udeg_irr_shape //.
    apply/Bigint.BIA.eq_big_seq => s /allshapesP is_s_s /=.
    move/perm_eq_size: (perm_eq_enum_udeg_irr_deg _ _ lt1n is_s_s) => ->.
    rewrite size_map size_alltuples_list Bigint.prodzE.
    rewrite mapi_map !Bigint.BIM.big_mapT (is_shape_size _ _ is_s_s) /=.
    rewrite (Bigint.BIM.big_nth (witness, 0) _ _ (zip _ _)).
    rewrite size_zip size_range ler_maxr -?ltzS ?ltzE ?ltzW //.
    rewrite (is_shape_size _ _ is_s_s) ler_minr //.
    apply/Bigint.BIM.eq_big_int => i /mem_range memi /=.
    rewrite /(\o) (nth_zip witness 0) /=; [rewrite size_range ler_maxr|].
    + by rewrite -ltzS ltzE ltzW.
    + by rewrite (is_shape_size _ _ is_s_s).
    by rewrite nth_range // -mem_range.
  qed.

  lemma enum_iudeg0 :
    enum_iudeg 0 = [].
  proof.
    apply/eq_in_filter_pred0 => p /enum_udegP [] + /deg_eq0 ->>.
    by rewrite /monic lc0 eq_sym RL.oner_neq0.
  qed.

  lemma enum_iudegP n p :
    p \in enum_iudeg n <=>
    (irreducible_poly p /\ monic p /\ deg p = n).
  proof. by rewrite /enum_iudeg mem_filter enum_udegP. qed.

  lemma uniq_enum_iudeg n :
    uniq (enum_iudeg n).
  proof. by rewrite filter_uniq; apply/uniq_enum_udeg. qed.

  lemma perm_eq_enum_iudeg k d :
    0 <= k =>
    1 < d =>
    perm_eq
      (enum_udeg_irr_deg k d)
      (map (PCM.big predT idfun) (undup_eqv perm_eq (alltuples k (enum_iudeg d)))).
  proof.
    move=> le0k lt1d; apply/uniq_perm_eq.
    + by apply/uniq_enum_udeg_irr_deg.
    + rewrite map_inj_in_uniq; last first.
      - apply/undup_eqv_uniq; [by apply/perm_eq_refl| |by apply/perm_eq_trans].
        by move=> ? ?; rewrite perm_eq_sym.
      move=> qs1 qs2 mem1 mem2 eq_.
      apply/(mem_undup_eqv_inj _ _ _ _ perm_eq_refl _ perm_eq_trans mem1 mem2).
      - by move=> ? ?; rewrite perm_eq_sym.
      move: eq_; pose p:= (PCM.big predT idfun qs1).
      move: {1 3}p (eq_refl p); rewrite /p => {p} p eq1 eq2.
      move: (mem_undup_eqv_mem _ perm_eq_refl _ perm_eq_trans _ _ mem1).
      - by move=> ? ?; rewrite perm_eq_sym.
      case/alltuplesP; rewrite ler_maxr // => size1 all1 {mem1}.
      move: (mem_undup_eqv_mem _ perm_eq_refl _ perm_eq_trans _ _ mem2).
      - by move=> ? ?; rewrite perm_eq_sym.
      case/alltuplesP; rewrite ler_maxr // => size2 all2 {mem2}.
      apply/(irredp_monic_dec_perm_eq p); apply/irredp_monic_decP; do!split.
      - by move: all1; apply/all_imp_in/allP => q /= _ /enum_iudegP.
      - rewrite eq1 -prodf_neq0; move: all1; apply/all_imp_in/allP => q /=.
        by move=> _ /enum_iudegP [] /irredp_neq0 + _; rewrite /predI /predC /predT /idfun.
      - rewrite -eq1; have ->: monic p; [|by rewrite scale1r].
        rewrite eq1 monic_prod; move: all1; apply/all_imp_in/allP => q /=.
        by move=> _ /enum_iudegP; rewrite /idfun.
      - by move: all2; apply/all_imp_in/allP => q /= _ /enum_iudegP.
      - rewrite eq2 -prodf_neq0; move: all2; apply/all_imp_in/allP => q /=.
        by move=> _ /enum_iudegP [] /irredp_neq0 + _; rewrite /predI /predC /predT /idfun.
      rewrite -eq2; have ->: monic p; [|by rewrite scale1r].
      rewrite eq2 monic_prod; move: all2; apply/all_imp_in/allP => q /=.
      by move=> _ /enum_iudegP; rewrite /idfun.
    move=> p; rewrite enum_udeg_irr_degP mapP; split=> [[] m_ [qs]|[qs]].
    + case=> dec_ [] <<- all_.
      move: (undup_eqv_mem _ perm_eq_refl _ perm_eq_trans
              (alltuples (size qs) (enum_iudeg d)) qs _).
      - by move=> ? ?; rewrite perm_eq_sym.
      - apply/alltuplesP; rewrite ler_maxr //=.
        move: all_; apply/all_imp_in/allP => q mem_ /= <<-.
        apply/enum_iudegP => /=; move/irredp_monic_decP: dec_.
        by case=> /allP /(_ _ mem_) [] ? ? _.
      case/hasP => rs [] mem_ eq_; exists rs; rewrite mem_ /=.
      rewrite -(PCM.eq_big_perm _ _ _ _ eq_) => {rs mem_ eq_}.
      case/irredp_monic_decP: dec_ => {all_} all_ [] _ ->.
      by rewrite m_ scale1r.
    case=> mem_ ->>; move: (mem_undup_eqv_mem _ perm_eq_refl _ perm_eq_trans _ _ mem_).
    + by move=> ? ?; rewrite perm_eq_sym.
    case/alltuplesP; rewrite ler_maxr // => [] <<- all_ {le0k mem_}; rewrite monic_prod /=.
    + by move: all_; apply/all_imp_in/allP => q mem_ /= /enum_iudegP; rewrite /idfun.
    exists qs => /=; rewrite irredp_monic_decP -prodf_neq0 lc_prod BigCf.BCM.big1_seq.
    + move=> q; rewrite /predT /(\o) /idfun /= => mem_; move/allP/(_ _ mem_): all_.
      by case/enum_iudegP => _ [] ->.
    rewrite scale1r /= -!all_predI; move: all_; apply/all_imp_in/allP.
    move=> q mem_; rewrite /predI /predC /predT /idfun /=.
    case/enum_iudegP => irr_ [] m_ <<-; rewrite irr_ m_ /=.
    by apply/irredp_neq0.
  qed.

  lemma size_enum_iudeg n :
    0 < n =>
    Bigint.BIA.big
      predT
      (fun s =>
        Bigint.BIM.bigi
          predT
          (fun i => Bigint.BIM.bigi
                      predT
                      ((+) (size (enum_iudeg (i + 1))))
                      0 (nth 0 s (i - 1))
                    %/ fact (nth 0 s (i - 1)))
          1 (n + 1))
      (allshapes n) =
    FT.card ^ n.
  proof.
    move=> lt0n; rewrite -size_enum_udeg_irr_deg //.
    apply/Bigint.BIA.eq_big_seq => s /allshapesP is_s_s /=.
    rewrite (range_addr 1 n 1) Bigint.BIM.big_mapT.
    apply/Bigint.BIM.eq_big_seq => i memi /=.
    move/allP/(_ (nth 0 s i) _): (is_shape_ge0 _ _ is_s_s); [|move=> le0_].
    + by apply/mem_nth/mem_range; rewrite (is_shape_size _ _ is_s_s).
    move: (perm_eq_enum_iudeg (nth 0 s i) (i + 2) _ _) => //.
    + by apply/ltr_subl_addr; move: memi; apply/mem_range_lt.
    move/perm_eq_size => ->; rewrite size_map /(\o) /=.
    case/ler_eqVlt: le0_ => [/eq_sym eq0_|lt0_].
    + by rewrite eq0_ alltuples_le0 //= fact0 // divz1 range_geq.
    rewrite uniq_size_undup_perm_eq //.
    + by apply/uniq_enum_iudeg.
    + by apply/ltzW.
    + by rewrite negb_and gtr_eqF.
    rewrite (IntID.addrC 2) addrAC; move: (size_ge0 (enum_iudeg (i + 2))) lt0_.
    pose a:= size _; pose b:= nth _ _ _; move: a b.
    move=> a b le0a lt0b {n lt0n s is_s_s i memi}.
    rewrite Bigint.BIM.big_predT_idfun -(range_addr a b a) (IntID.addrC b).
    case/ler_eqVlt: le0a => [<<-/=|lt0a].
    + by rewrite bin_gt ?ltzE // range_ltn.
    apply/(IntID.mulfI (fact b * fact (a - 1))).
    + by apply/gtr_eqF/mulr_gt0; apply/fact_gt0.
    move: (eq_bin_div (a + b - 1) b _).
    + by rewrite ltzW //= -ltzS /= -ltr_subl_addr.
    rewrite (IntID.addrAC _ (-1)) addrK /= => ->.
    rewrite (IntID.mulrC (fact _)) mulrAC -mulrA divzK.
    + by apply/dvd_fact_prod_range; rewrite addrAC.
    rewrite /fact /= (range_cat a 1 (a + b)).
    + by move/ltzE: lt0a.
    + by apply/ler_subl_addl/ltzW.
    by rewrite Bigint.BIM.big_cat.
  qed.

  lemma eqI_size_enum_iudeg n :
    0 < n =>
    Counting_Argument.I n FT.card = size (enum_iudeg (n + 1)).
  proof.
    rewrite -(IntID.subrK n 1); pose m:= n - 1; move: m => {n} n /ltzS.
    elim/sintind: n => n le0n /= IHn.
    move: (Counting_Argument.eqI (n + 1) _ _ FCR.card_gt1); [by apply/ltzS|].
    rewrite -size_enum_iudeg /=; [by apply/ltzS|].
    rewrite !(Bigint.BIA.big_rem _ _ (allshapes _) (shape (cc_perm (range 0 (n + 1))))).
    + apply/allshapesP/is_shapeP; exists (cc_perm (range 0 (n + 1))) => /=.
      by apply/is_perm_cc; [apply/ltzS|apply/perm_eq_refl].
    + apply/allshapesP/is_shapeP; exists (cc_perm (range 0 (n + 1))) => /=.
      by apply/is_perm_cc; [apply/ltzS|apply/perm_eq_refl].
    rewrite /(predT (shape _)) /= !rem_filter ?allshapes_uniq //.
    pose sI:= Bigint.BIA.big _ _ _; pose sE:= Bigint.BIA.big _ _ _.
    have ->: sI = sE; [rewrite /sI /sE|move/IntID.addIr]; move=> {sI sE}.
    + apply/Bigint.BIA.eq_big_seq => s; rewrite mem_filter /predC1.
      case=> neqs_ /allshapesP is_s_s /=; apply/Bigint.BIM.eq_big_seq.
      move=> i memi /=; congr; congr; apply/Bigint.BIM.eq_big_seq.
      move=> j memj; congr; move: memi; rewrite (rangeSr _ (n + 1)).
      - by apply/ler_subl_addr.
      rewrite mem_rcons /=; case=> [->>/=|memi]; last first.
      - by move/( _ (i - 1)): IHn; rewrite -mem_range mem_range_subr memi.
      move: is_s_s neqs_ memj => /= /is_shapeP [] p [] is_p_p <<-.
      move/allP/(_ (nth 0 (shape p) n) _): (shape_ge0 p).
      - by apply/mem_nth; rewrite size_shape (size_is_perm _ _ is_p_p) ltzS.
      case/ler_eqVlt => [<-|]; [by rewrite (range_geq 0 0)|].
      rewrite (cc_shapeW _ _ _ is_p_p); case=> c [] eq_ ->>.
      rewrite (cc_shapeP (n + 1) c) //=; [by apply/ltzS|].
      rewrite (cc_shapeP (n + 1) (range 0 (n + 1))) //=; [by apply/ltzS|].
      by apply/perm_eq_refl.
    rewrite (cc_shapeP (n + 1)) /=; [by apply/ltzS|by apply/perm_eq_refl|].
    rewrite (rangeSr _ (n + 1)); [by apply/ler_subl_addr|].
    rewrite !Bigint.BIM.big_rcons /(predT (n + 1)) /=.
    pose sI:= Bigint.BIM.big _ _ _; pose xI:= _ %/ _.
    pose sE:= Bigint.BIM.big _ _ _; pose xE:= _ %/ _.
    have ->/=: sI = 1; rewrite /sI => {sI}.
    + rewrite Bigint.BIM.big1_seq // => i [] _ memi /=.
      rewrite nth_rcons size_nseq ler_maxr // ltzE /= -ltzS.
      case/mem_range: (memi) => _ -> /=.
      rewrite nth_nseq -?mem_range ?mem_range_subr //.
      by rewrite range_geq // Bigint.BIM.big_nil fact0.
    have ->/=: sE = 1; rewrite /sE => {sE}.
    + rewrite Bigint.BIM.big1_seq // => i [] _ memi /=.
      rewrite nth_rcons size_nseq ler_maxr // ltzE /= -ltzS.
      case/mem_range: (memi) => _ -> /=.
      rewrite nth_nseq -?mem_range ?mem_range_subr //.
      by rewrite range_geq // Bigint.BIM.big_nil fact0.
    rewrite /xI /xE; rewrite nth_rcons size_nseq ler_maxr //=.
    by rewrite fact1 !divz1 range_ltn // range_geq.
  qed.

  lemma exists_iu_le_deg (n : int) :
    exists p , n < deg p /\ irreducible_poly p /\ monic p.
  proof.
    rewrite -negbK negb_exists /=; apply/negP => forall_.
    case: (irredp_monic_decW (PCM.big predT idfun (rem poly0 (enum_ledeg n)) * X + poly1)) => + _.
    rewrite rem_filter ?uniq_enum_ledeg //; rewrite scaled_monicP.
    pose r:= (PCM.big _ _ _); have: r <> poly0; rewrite /r => {r}.
    + rewrite -prodf_neq0; apply/allP => q /mem_filter [] + _.
      by rewrite /predC1 /predC /predI /predT /idfun.
    move=> neq_0; pose r:= (_ + poly1); have: r <> poly0; rewrite /r => {r}.
    + apply/negP => /(congr1 deg); rewrite deg0 degDl.
      - by rewrite deg1 degM ?nz_polyX // degX /= -ltr_subl_addr deg_gt0.
      rewrite /=; apply/gtr_eqF; rewrite deg_gt0.
      by apply/IDPoly.mulf_neq0 => //; apply/nz_polyX.
    move=> neq_0_; rewrite neq_0_ /=; apply/negP.
    case; case=> [|q qs]; [rewrite -irredp_monic_dec_nil /= gtr_eqF //|].
    + rewrite degDl; [by rewrite deg1 degM ?nz_polyX // degX /= -ltr_subl_addr deg_gt0|].
      by rewrite degM ?nz_polyX // degX /= -ltr_subl_addr deg_gt0.
    rewrite -irredp_monic_dec_cons => -[] dvdp_ [] irr_ [] m_ dec_.
    case: (deg q <= n) => [le_n|/ltrNge ltn_]; [move: dvdp_; rewrite (PCM.big_rem _ _ _ q)|].
    + by rewrite mem_filter enum_ledegP le_n /predC1 irredp_neq0.
    + rewrite /(predT q) /(idfun q) /=; apply/negP => /dvdp_add_eq.
      rewrite -PolyComRing.mulrA dvdp_mulIl eq_sym eqT dvdp1 /=.
      by rewrite gtr_eqF // irredp_poly_deg.
    by move: forall_ => /(_ q).
  qed.
end PolyFiniteField.


abstract theory FFIrrPolyExt.
  type t, st.

  clone include PolyFiniteField with
    type t <- st
    rename [theory] "RL"      as "SRL"
                    "ZModStr" as "ZModSStr"
                    "CRStr"   as "CRSStr"
                    "IDStr"   as "IDSStr"
                    "FStr"    as "FSStr"
                    "FT"      as "SFT"
                    "FZMod"   as "FZModS"
                    "FCR"     as "FCRS"
                    "FID"     as "FIDS"
                    "FF"      as "FFS"
                    "UZL"     as "UZLS"
                    "UStr"    as "USStr"
                    "USub"    as "USubS"
                    "FUT"     as "FUTS"
                    "UZModCR" as "USZModCR"
                    "FUZMod"  as "FUSZMod"
           [type]   "uz"      as "uzs".

  import PID.
  import P.
  import BigPoly.
  import IdealP.

  op p : poly.

  axiom irredp_p : irreducible_poly p.

  clone import FieldQuotient as IFQ with
    type qT <= t,
    op p    <= idgen [p],
    op CRQ.invr <= (fun x => choiceb (fun y => CRQ.( * ) y x = CRQ.oner) CRQ.zeror),
    pred CRQ.unit <= (fun x => x <> CRQ.zeror)
  proof MaximalIdealAxioms.*, CRQ.*.

  realize MaximalIdealAxioms.ideal_p by apply/ideal_idgen.

  realize MaximalIdealAxioms.neq_p_idT.
  proof.
    apply/negP => /fun_ext /(_ poly1); rewrite mem_idT eqT.
    rewrite mem_idgen1 /= negb_exists => q /=; apply/negP.
    move/(congr1 deg); rewrite deg1 eq_sym.
    case: (q = poly0) => [->>|neqq0]; [by rewrite PolyComRing.mul0r deg0|].
    rewrite degM //=; [by apply/irredp_neq0/irredp_p|].
    apply/gtr_eqF/ltr_subr_addr => /=; apply/ltzE.
    move/deg_gt0/ltzE: neqq0 irredp_p => le1 /irredp_poly_deg /ltzE le2.
    by move: (ler_add _ _ _ _ le1 le2).
  qed.

  realize MaximalIdealAxioms.max_p.
  proof.
    split; [by apply/ideal_idgen|split; [by apply/MaximalIdealAxioms.neq_p_idT|]].
    move=> I iI neqIT forall_; apply/fun_ext => q; rewrite eq_iff; split.
    + by apply/forall_.
    move=> Iq; apply/mem_idgen1; move/(_ _ (mem_idgen1_gen FFIrrPolyExt.p)): forall_ => Ip.
    case: irredp_p => lt1_ /(_ (gcdp FFIrrPolyExt.p q) _ (dvdp_gcdl FFIrrPolyExt.p q)).
    + move: neqIT; apply/implybNN; rewrite deg_eq1 => -[c] [] neqc0 eqc_.
      rewrite -(ideal_eq1P _ (gcdp FFIrrPolyExt.p q)) //.
      - rewrite eqc_; split; [by rewrite degC neqc0|].
        by rewrite polyCE /= -SRL.unitfE.
      case: (Bezoutp FFIrrPolyExt.p q) => u v eqp_; move: eqp_ (eqp_).
      move/eqp_size; rewrite {1}eqc_ degC neqc0 /= deg_eq1.
      case=> d [] neqd0 eqd_/eqp_eq.
      move/(congr1 (P.( ** ) (SRL.invr (lc (u * FFIrrPolyExt.p + v * q))))).
      rewrite !scalepA SRL.mulVr; [by apply/SRL.unitfE; rewrite eqd_ lcC|].
      rewrite scale1r => <-; rewrite scalepDr !scalerAl.
      by apply/idealD => //; apply/idealMl.
    case=> _ dvdp_; move: (dvdp_trans _ _ _ dvdp_ (dvdp_gcdr FFIrrPolyExt.p q)).
    by rewrite -ulc_dvdpP // -SRL.unitfE lc_eq0 irredp_neq0 // irredp_p.
  qed.

  realize CRQ.mulVr.
  proof.
    have pip: pi FFIrrPolyExt.p = CRQ.zeror.
    + apply/eqv_pi; rewrite eqv_sym; apply/mem_idgen1.
      by exists poly1; rewrite PolyComRing.subr0 PolyComRing.mul1r.
    move=> x neqx0; pose P:= (fun y => (_ y _) = _).
    move: (choicebP P CRQ.zeror _); rewrite /P => {P} //.
    move: (PID.Bezout_coprimepP (modp (repr x) FFIrrPolyExt.p) FFIrrPolyExt.p).
    rewrite -gcdp_eqp1; case: irredp_p => lt1_.
    move/(_ (gcdp (modp (repr x) FFIrrPolyExt.p) FFIrrPolyExt.p)).
    rewrite dvdp_gcdr /= => /implybNN /= /(_ _).
    + apply/negP => /eqp_size /=; apply/ltr_eqF.
      apply/(ler_lt_trans _ _ _ (leq_gcdpl _ _ _)).
      - rewrite modp_eq0P; move: neqx0; apply/implybNN.
        rewrite -ulc_dvdpP; [by rewrite -SRL.unitfE lc_eq0 -deg_eq0; apply/gtr_eqF/ltzE/ltzW|].
        by case=> q /(congr1 pi); rewrite reprK -mulE pip mulE PolyComRing.mulr0.
      by rewrite ltn_modp -deg_eq0; apply/gtr_eqF/ltzE/ltzW.
    move/deg_eqp => ->; rewrite eqT => -[u v].
    rewrite -deg_eqp deg_eq1 => -[c] [] neqc0.
    move/(congr1 (( ** ) (SRL.invr c))); rewrite scalepDr !scalerAl.
    rewrite (scalepE _ (polyC _)) -polyCM SRL.mulVr -?SRL.unitfE //.
    move: (ulc_divp_eq FFIrrPolyExt.p (repr x) _).
    + by rewrite -SRL.unitfE lc_eq0 irredp_neq0 // irredp_p.
    rewrite PolyComRing.addrC -PolyComRing.subr_eq => <-; rewrite PolyComRing.mulrDr.
    rewrite PolyComRing.mulrN -PolyComRing.mulNr -PolyComRing.addrA.
    rewrite PolyComRing.mulrA -PolyComRing.mulrDl.
    move/(congr1 pi); rewrite -/IFQ.oner => <-; rewrite -addE.
    rewrite -(mulE _ FFIrrPolyExt.p) pip (mulE _ poly0) PolyComRing.mulr0.
    by rewrite addE PolyComRing.addr0 -mulE reprK; exists (pi ((SRL.invr c) ** u)).
  qed.

  realize CRQ.unitP.
  proof.
    move=> ? x eq_; apply/negP => ->>; move: eq_.
    rewrite -(reprK x) mulE PolyComRing.mulr0 -eqv_pi.
    rewrite /eqv mem_idgen1 => -[q] /(congr1 deg) /=.
    rewrite PolyComRing.subr0 deg1; case (q = poly0) => [->>|neqq0].
    + by rewrite PolyComRing.mul0r deg0.
    rewrite degM // ?irredp_neq0 ?irredp_p // ltr_eqF // ltzE -ltzS ltzE /=.
    move: (deg_eq0 q) (irredp_poly_deg _ irredp_p); rewrite neqq0 /= => {neqq0}.
    move/ltr_total; rewrite ltrNge ge0_deg /= => /ltzE le1 /ltzE le2.
    by move: (ler_add _ _ _ _ le1 le2).
  qed.

  realize CRQ.unitout.
  proof.
    move=> ? /= ->>; pose P:= (fun y => (_ y _) = _).
    apply/(choiceb_dfl P CRQ.zeror); rewrite /P => {P} x.
    rewrite /(CRQ.( * )) -(reprK x) mulE PolyComRing.mulr0 -eqv_pi.
    rewrite /eqv mem_idgen1; apply/negP => -[q] /(congr1 deg) /=.
    rewrite PolyComRing.subr0 deg1; case (q = poly0) => [->>|neqq0].
    + by rewrite PolyComRing.mul0r deg0.
    rewrite degM // ?irredp_neq0 ?irredp_p // ltr_eqF // ltzE -ltzS ltzE /=.
    move: (deg_eq0 q) (irredp_poly_deg _ irredp_p); rewrite neqq0 /= => {neqq0}.
    move/ltr_total; rewrite ltrNge ge0_deg /= => /ltzE le1 /ltzE le2.
    by move: (ler_add _ _ _ _ le1 le2).
  qed.

  clone include SubFiniteField with
    type   t        <- t,
    type   st       <- st,
    type uzs        <- uzs,
    theory TRL      <= IFQ.FQ,
    theory SRL      <- SRL,
    theory ZModSStr <- ZModSStr,
    theory CRSStr   <- CRSStr,
    theory IDSStr   <- IDSStr,
    theory FSStr    <- FSStr,
    theory SFT      <- SFT,
    theory FZModS   <- FZModS,
    theory FCRS     <- FCRS,
    theory FIDS     <- FIDS,
    theory FFS      <- FFS,
    theory UZLS     <- UZLS,
    theory USStr    <- USStr,
    theory USubS    <- USubS,
    theory USZModCR <- USZModCR,
    theory FUSZMod  <- FUSZMod,
    theory FUTS     <- FUTS,
    op TFT.enum     <= map pi (enum_ledeg (deg p - 1)),
    pred Sub.P      <= (fun x => exists c , x = pi (polyC c)),
    op Sub.insub    <= (fun x =>
                         if (exists c , x = pi (polyC c))
                         then Some ((modp (repr x) FFIrrPolyExt.p).[0])
                         else None),
    op Sub.val      <= (fun c => pi (polyC c)),
    op Sub.wsT      <= pi (polyC witness)
    rename [theory] "SRL"      as "Gone"
                    "ZModSStr" as "Gone"
                    "CRSStr"   as "Gone"
                    "IDSStr"   as "IDSStrGone"
                    "FSStr"    as "Gone"
                    "SFT"      as "Gone"
                    "FZModS"   as "Gone"
                    "FCRS"     as "Gone"
                    "FIDS"     as "Gone"
                    "FFS"      as "Gone"
                    "UZLS"     as "Gone"
                    "USStr"    as "Gone"
                    "USubS"    as "Gone"
                    "FUTS"     as "Gone"
                    "USZModCR" as "Gone"
                    "FUSZMod"  as "Gone"
  proof Sub.*, SZMod.*, SCR.*, TFT.*.

  realize Sub.insubN.
  proof. by move=> x ->. qed.

  realize Sub.insubT.
  proof.
    move=> ? exists_; rewrite exists_ /=; case: exists_ => c ->>.
    rewrite -eqv_pi eqv_sym /eqv mem_idgen1; exists poly0.
    rewrite -polyCN -polyCD PolyComRing.mul0r eq_polyC0.
    rewrite SRL.subr_eq0; move: (eqv_repr (polyC c)).
    rewrite eqv_sym /eqv mem_idgen1 => -[q].
    rewrite PolyComRing.subr_eq => ->; rewrite ulc_modp_addl_mul_small.
    + by rewrite -SRL.unitfE lc_eq0 irredp_neq0 // irredp_p.
    + by apply/(ler_lt_trans _ _ _ (degC_le _))/irredp_poly_deg/irredp_p.
    by rewrite polyCE.
  qed.

  realize Sub.valP.
  proof. by move=> c; exists c. qed.

  realize Sub.valK.
  proof.
    move=> c; rewrite ifT; [by exists c|].
    congr; move: (eqv_repr (polyC c)).
    rewrite eqv_sym /eqv mem_idgen1 => -[q].
    rewrite PolyComRing.subr_eq => ->; rewrite ulc_modp_addl_mul_small.
    + by rewrite -SRL.unitfE lc_eq0 irredp_neq0 // irredp_p.
    + by apply/(ler_lt_trans _ _ _ (degC_le _))/irredp_poly_deg/irredp_p.
    by rewrite polyCE.
  qed.

  realize Sub.insubW.
  proof.
    rewrite ifT; [by exists witness|].
    congr; move: (eqv_repr (polyC witness)).
    rewrite eqv_sym /eqv mem_idgen1 => -[q].
    rewrite PolyComRing.subr_eq => ->; rewrite ulc_modp_addl_mul_small.
    + by rewrite -SRL.unitfE lc_eq0 irredp_neq0 // irredp_p.
    + by apply/(ler_lt_trans _ _ _ (degC_le _))/irredp_poly_deg/irredp_p.
    by rewrite polyCE.
  qed.

  realize SZMod.val0.
  proof. by trivial. qed.

  realize SZMod.valD.
  proof. by move=> ? ?; rewrite polyCD addE. qed.

  realize SCR.val1.
  proof. by trivial. qed.

  realize SCR.valM.
  proof. by move=> ? ?; rewrite polyCM mulE. qed.

  realize TFT.enum_spec.
  proof.
    move=> x; rewrite (count_rem _ _ x) -(reprK x).
    + apply/mapP; exists (modp (repr x) p).
      rewrite enum_ledegP -ltzS /= ltn_modp irredp_neq0 ?irredp_p //=.
      rewrite -eqv_pi eqv_sym /eqv mem_idgen1; exists (divp (repr x) p).
      rewrite PolyComRing.subr_eq -ulc_divp_eq // -SRL.unitfE.
      by rewrite lc_eq0 irredp_neq0 // irredp_p.
    rewrite /(pred1 _ _) /= b2i1 eq_sym addrC -subr_eq eq_sym /=.
    rewrite rem_filter ?map_inj_in_uniq ?uniq_enum_ledeg //.
    + move=> q r /enum_ledegP /ltzS /= ltq_ /enum_ledegP /ltzS /= ltr_.
      move/eqv_pi; rewrite eqv_sym /eqv => /mem_idgen1 [u].
      rewrite PolyComRing.subr_eq => /(congr1 (transpose modp p)) /=.
      rewrite ulc_modp_addl_mul_small // ?modp_small //.
      by rewrite -SRL.unitfE lc_eq0 irredp_neq0 // irredp_p.
    by rewrite -mem_count_eq0 mem_filter mapP /predC1.
  qed.

  lemma eqn : SFF.n = deg p - 1.
  proof.
    apply/(ieexprIn _ SFT.card_gt0).
    + by apply/gtr_eqF/FCRS.card_gt1.
    + by apply/ltzW/SFF.lt0n.
    + by apply/ltzS/ltzE/ltzW => /=; apply/irredp_poly_deg/irredp_p.
    rewrite -SFF.eq_card_pow_n /TFT.card size_map size_enum_ledeg //.
    by apply/ltzS/ltzE/ltzW => /=; apply/irredp_poly_deg/irredp_p.
  qed.
end FFIrrPolyExt.
