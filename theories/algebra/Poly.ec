(* -------------------------------------------------------------------- *)
require import AllCore Finite Distr DList List.
require import Ring IntMin Bigalg StdBigop StdOrder Ideal.
require (*--*) Subtype.
(*---*) import Bigint IntID IntOrder.

(* ==================================================================== *)
abstract theory PolyComRing.
type coeff.

clone import ComRing as Coeff with type t <= coeff.

clone import BigComRing as BigCf
  with theory CR <- Coeff

  rename [theory] "BAdd" as "BCA"
         [theory] "BMul" as "BCM".

(* -------------------------------------------------------------------- *)
type prepoly = int -> coeff.

op ispoly (p : prepoly) =
      (forall c, c < 0 => p c = zeror)
    /\ (exists d, forall c, (d < c)%Int => p c = zeror).

subtype poly = { p : prepoly | ispoly p }
  rename "to_poly", "of_poly".

realize inhabited.
proof. by exists (fun _ => zeror). qed.

op "_.[_]" (p : poly) (i : int) = (of_poly p) i.

lemma lt0_coeff p c : c < 0 => p.[c] = zeror.
proof.
by move=> lt0_c; rewrite /"_.[_]"; case: (of_polyP p) => /(_ _ lt0_c).
qed.

op deg (p : poly) = argmin idfun (fun i => forall j, (i <= j)%Int => p.[j] = zeror).

lemma degP p c :
     0 < c
  => p.[c-1] <> zeror
  => (forall i, c <= i => p.[i] = zeror)
  => deg p = c.
proof.
move=> ge0_c nz_p_cB1 degc @/deg; apply: argmin_eq => /=.
- by apply/ltrW. - by apply: degc.
move=> j [ge0_j lt_jc]; rewrite negb_forall /=.
by exists (c-1); apply/negP => /(_ _); first by move=> /#.
qed.

lemma deg_leP p c : 0 <= c =>
  (forall (i : int), c <= i => p.[i] = zeror) => deg p <= c.
proof.
move=> ge0_c; apply: contraLR; rewrite lerNgt /= => lec.
by have @{1}/deg /argmin_min /=: 0 <= c < deg p by done.
qed.

lemma gedeg_coeff (p : poly) (c : int) : deg p <= c => p.[c] = zeror.
proof.
move=> le_p_c; pose P p i := forall j, (i <= j)%Int => p.[j] = zeror.
case: (of_polyP p) => [wf_p [d hd]]; move: (argminP idfun (P p)).
move/(_ (max (d+1) 0) _ _) => /=; first exact: maxrr.
- by move=> j le_d_j; apply: hd => /#.
by apply; apply: le_p_c.
qed.

lemma ge0_deg p : 0 <= deg p.
proof. rewrite /deg &(ge0_argmin). qed.

(* -------------------------------------------------------------------- *)
abbrev lc (p : poly) = p.[deg p - 1].

(* -------------------------------------------------------------------- *)
op prepolyC  (c   : coeff) = fun i => if i = 0 then c else zeror.
op prepolyXn (k   : int  ) = fun i => if 0 <= k /\ i = k then oner else zeror.
op prepolyD  (p q : poly ) = fun i => p.[i] + q.[i].
op prepolyN  (p   : poly ) = fun i => - p.[i].

op prepolyM (p q : poly) = fun k =>
  BCA.bigi predT (fun i => p.[i] * q.[k-i]) 0 (k+1).

op prepolyZ (z : coeff) (p : poly) = fun k =>
  z * p.[k].

lemma ispolyC (c : coeff) : ispoly (prepolyC c).
proof.
split=> @/prepolyC [c' ?|]; first by rewrite ltr_eqF.
by exists 0 => c' gt1_c'; rewrite gtr_eqF.
qed.

lemma ispolyXn (k : int) : ispoly (prepolyXn k).
proof.
split=> @/prepolyXn [c lt0_c|].
+ by case: (0 <= k) => //= ge0_k; rewrite ltr_eqF //#.
+ by exists k => c gt1_c; rewrite gtr_eqF.
qed.

lemma ispolyN (p : poly) : ispoly (prepolyN p).
proof.
split=> @/prepolyN [c lt0_c|]; first by rewrite oppr_eq0 lt0_coeff.
by exists (deg p) => c => /ltrW /gedeg_coeff ->; rewrite oppr0.
qed.

lemma ispolyD (p q : poly) : ispoly (prepolyD p q).
proof.
split=> @/prepolyD [c lt0_c|]; first by rewrite !lt0_coeff // addr0.
by exists (1 + max (deg p) (deg q)) => c le; rewrite !gedeg_coeff ?addr0 //#.
qed.

lemma ispolyM (p q : poly) : ispoly (prepolyM p q).
proof.
split => @/prepolyM [c lt0_c|]; 1: by rewrite BCA.big_geq //#.
exists (deg p + deg q + 1) => c ltc; rewrite BCA.big_seq BCA.big1 //= => i.
rewrite mem_range => -[gt0_i lt_ic]; case: (p.[i] = zeror).
- by move=> ->; rewrite mul0r.
move/(contra _ _ (gedeg_coeff p i)); rewrite lerNgt /= => lt_ip.
by rewrite mulrC gedeg_coeff ?mul0r //#.
qed.

lemma ispolyZ z p : ispoly (prepolyZ z p).
proof.
split => @/prepolyZ [c lt0_c|]; 1: by rewrite lt0_coeff //mulr0.
by exists (deg p + 1) => c gtc; rewrite gedeg_coeff ?mulr0 //#.
qed.

lemma poly_eqP (p q : poly) : p = q <=> (forall c, 0 <= c => p.[c] = q.[c]).
proof.
split=> [->//|eq_coeff]; apply/of_poly_inj/fun_ext => c.
case: (c < 0) => [lt0_c|/lerNgt /=]; last by apply: eq_coeff.
by rewrite -/"_.[_]" !lt0_coeff.
qed.

op polyC  c   = to_polyd (prepolyC  c).
op polyXn k   = to_polyd (prepolyXn k).
op polyN  p   = to_polyd (prepolyN  p).
op polyD  p q = to_polyd (prepolyD  p q).
op polyM  p q = to_polyd (prepolyM p q).
op polyZ  z p = to_polyd (prepolyZ z p).

abbrev poly0  = polyC  zeror.
abbrev poly1  = polyC  oner.
abbrev polyX  = polyXn 1.
abbrev X      = polyXn 1.
abbrev ( + )  = polyD.
abbrev [ - ]  = polyN.
abbrev ( * )  = polyM.
abbrev ( ** ) = polyZ.

abbrev ( - ) p q = p + (-q).

(* -------------------------------------------------------------------- *)
lemma coeffE p k : ispoly p => (to_polyd p).[k] = p k.
proof. by move=> ?; rewrite /"_.[_]" to_polydK. qed.

lemma polyCE c k : (polyC c).[k] = if k = 0 then c else zeror.
proof. by rewrite coeffE 1:ispolyC. qed.

lemma polyXE k : X.[k] = if k = 1 then oner else zeror.
proof. by rewrite coeffE 1:ispolyXn. qed.

lemma poly0E k : poly0.[k] = zeror.
proof. by rewrite polyCE if_same. qed.

lemma polyNE p k : (-p).[k] = - p.[k].
proof. by rewrite coeffE 1:ispolyN. qed.

lemma polyDE p q k : (p + q).[k] = p.[k] + q.[k].
proof. by rewrite coeffE 1:ispolyD. qed.

lemma polyME p q k : (p * q).[k] =
  BCA.bigi predT (fun i => p.[i] * q.[k-i]) 0 (k+1).
proof. by rewrite coeffE 1:ispolyM. qed.

lemma polyMXE p k : (p * X).[k] = p.[k-1].
proof.
case: (k < 0) => [lt0_k|]; first by rewrite !lt0_coeff //#.
rewrite ltrNge => /= ge0_k; rewrite polyME; move: ge0_k.
rewrite ler_eqVlt => -[<-|gt0_k] /=.
- by rewrite BCA.big_int1 /= polyXE /= mulr0 lt0_coeff.
rewrite (BCA.bigD1 _ _ (k-1)) ?mem_range 1:/# 1:range_uniq /=.
rewrite opprB addrCA /= polyXE /= mulr1 BCA.big1 // ?addr0 //.
move=> i @/predC1 nei /=; rewrite polyXE subr_eq.
by rewrite (IntID.addrC 1) -subr_eq (eq_sym _ i) nei /= mulr0.
qed.

lemma polyZE z p k : (z ** p).[k] = z * p.[k].
proof. by rewrite coeffE 1:ispolyZ. qed.

hint rewrite coeffpE : poly0E polyDE polyNE polyME polyZE.

(* -------------------------------------------------------------------- *)
lemma polyCN (c : coeff) : polyC (- c) = - (polyC c).
proof.
apply/poly_eqP=> i ge0_i; rewrite !(coeffpE, polyCE).
by case: (i = 0) => // _; rewrite oppr0.
qed.

(* -------------------------------------------------------------------- *)
lemma polyCD (c1 c2 : coeff) : polyC (c1 + c2) = polyC c1 + polyC c2.
proof.
apply/poly_eqP=> i ge0_i; rewrite !(coeffpE, polyCE).
by case: (i = 0) => // _; rewrite addr0.
qed.

(* -------------------------------------------------------------------- *)
lemma polyCM (c1 c2 : coeff) : polyC (c1 * c2) = polyC c1 * polyC c2.
proof.
apply/poly_eqP=> i ge0_i; rewrite !(coeffpE, polyCE).
case: (i = 0) => [->|ne0_i]; first by rewrite BCA.big_int1 /= !polyCE.
rewrite BCA.big_seq BCA.big1 ?addr0 //= => j /mem_range rg_j.
rewrite !polyCE; case: (j = 0) => [->>/=|]; last by rewrite mul0r.
by rewrite ne0_i /= mulr0.
qed.

(* -------------------------------------------------------------------- *)
clone import Ring.ZModule as ZPoly with
  type t     <- poly ,
    op zeror <- poly0,
    op (+)   <- polyD,
    op [-]   <- polyN
  proof * remove abbrev (-).

realize addrA.
proof. by move=> p q r; apply/poly_eqP=> c; rewrite !coeffpE addrA. qed.

realize addrC.
proof. by move=> p q; apply/poly_eqP=> c; rewrite !coeffpE addrC. qed.

realize add0r.
proof. by move=> p; apply/poly_eqP => c; rewrite !coeffpE add0r. qed.

realize addNr.
proof. by move=> p; apply/poly_eqP => c; rewrite !coeffpE addNr. qed.

clear [ZPoly.* ZPoly.AddMonoid.*].

(* -------------------------------------------------------------------- *)
lemma scale0p p : zeror ** p = poly0.
proof. by apply/poly_eqP=> i ge0_i; rewrite !coeffpE mul0r. qed.

(* -------------------------------------------------------------------- *)
lemma scalep0 c : c ** poly0 = poly0.
proof. by apply/poly_eqP=> i ge0_i; rewrite !coeffpE mulr0. qed.

(* -------------------------------------------------------------------- *)
lemma scale1p p : oner ** p = p.
proof. by apply/poly_eqP=> i ge0_i; rewrite !coeffpE mul1r. qed.

(* -------------------------------------------------------------------- *)
lemma scalep1 c : c ** poly1 = polyC c.
proof.
apply/poly_eqP=> i ge0_i; rewrite !coeffpE !polyCE.
by case: (i = 0) => _; [rewrite mulr1|rewrite mulr0].
qed.

(* -------------------------------------------------------------------- *)
lemma scaleNp (c : coeff) p : (-c) ** p = - (c ** p).
proof. by apply/poly_eqP=> i ge0_i; rewrite !coeffpE mulNr. qed.

(* -------------------------------------------------------------------- *)
lemma scalepN (c : coeff) p : c ** (-p) = - (c ** p).
proof. by apply/poly_eqP=> i ge0_i; rewrite !coeffpE mulrN. qed.

(* -------------------------------------------------------------------- *)
lemma scalepA (c1 c2 : coeff) p : c1 ** (c2 ** p) = (c1 * c2) ** p.
proof. by apply/poly_eqP=> i ge0_i; rewrite !coeffpE mulrA. qed.

(* -------------------------------------------------------------------- *)
lemma scalepDr (c : coeff) p q : c ** (p + q) = (c ** p) + (c ** q).
proof. by apply/poly_eqP=> i ge0_i; rewrite !coeffpE mulrDr. qed.

(* -------------------------------------------------------------------- *)
lemma scalepBr (c : coeff) p q : c ** (p - q) = (c ** p) - (c ** q).
proof. by rewrite scalepDr scalepN. qed.

(* -------------------------------------------------------------------- *)
lemma scalepDl (c1 c2 : coeff) p : (c1 + c2) ** p = (c1 ** p) + (c2 ** p).
proof. by apply/poly_eqP=> i ge0_i; rewrite !coeffpE mulrDl. qed.

(* -------------------------------------------------------------------- *)
lemma scalepBl (c1 c2 : coeff) p : (c1 - c2) ** p = (c1 ** p) - (c2 ** p).
proof. by rewrite scalepDl scaleNp. qed.

(* -------------------------------------------------------------------- *)
lemma scalepE (c : coeff) p : c ** p = polyC c * p.
proof.
apply/poly_eqP=> i ge0_i; rewrite !coeffpE /=.
rewrite BCA.big_int_recl //= polyCE /=.
rewrite BCA.big_seq BCA.big1 ?addr0 //= => j /mem_range.
by case=> ge0_j _; rewrite polyCE addz1_neq0 //= mul0r.
qed.

(* -------------------------------------------------------------------- *)
lemma degC c : deg (polyC c) = if c = zeror then 0 else 1.
proof.
case: (c = zeror) => [->|nz_c]; last first.
- apply: degP => //=; first by rewrite polyCE.
  by move=> i ge1_i; rewrite polyCE gtr_eqF //#.
rewrite /deg; apply: argmin_eq => //=.
- by move=> j _; rewrite poly0E.
- by move=> j; apply: contraL => _ /#.
qed.

lemma degC_le c : deg (polyC c) <= 1.
proof. by rewrite degC; case: (c = zeror). qed.

lemma lcC c : lc (polyC c) = c.
proof. by rewrite polyCE degC; case: (c = zeror) => [->|]. qed.

lemma lc0 : lc poly0 = zeror.
proof. by apply: lcC. qed.

lemma lc1 : lc poly1 = oner.
proof. by apply: lcC. qed.

lemma deg0 : deg poly0 = 0.
proof. by rewrite degC. qed.

lemma deg1 : deg poly1 = 1.
proof.
apply: degP => //=; first by rewrite polyCE /= oner_neq0.
by move=> c ge1_c; rewrite polyCE gtr_eqF //#.
qed.

lemma deg_eq0 p : (deg p = 0) <=> (p = poly0).
proof.
split=> [z_degp|->]; last by rewrite deg0.
apply/poly_eqP=> c ge0_c; rewrite poly0E.
by apply/gedeg_coeff; rewrite z_degp.
qed.

lemma degX : deg X = 2.
proof.
apply/degP=> //=; first by rewrite polyXE /= oner_neq0.
by move=> c ge2_c; rewrite polyXE gtr_eqF //#.
qed.

lemma nz_polyX : X <> poly0.
proof. by rewrite -deg_eq0 degX. qed.

lemma lcX : lc X = oner.
proof. by rewrite degX /= polyXE. qed.

lemma deg_ge1 p : (1 <= deg p) <=> (p <> poly0).
proof. by rewrite -deg_eq0 eqr_le ge0_deg /= (lerNgt _ 0) /#. qed.

lemma deg_gt0 p : (0 < deg p) <=> (p <> poly0).
proof. by rewrite -deg_ge1 /#. qed.

lemma deg_eq1 p : (deg p = 1) <=> (exists c, c <> zeror /\ p = polyC c).
proof.
split=> [eq1_degp|[c [nz_c ->>]]]; last first.
+ by apply: degP => //= => [|i ge1_i]; rewrite polyCE //= gtr_eqF /#.
have pC: forall i, 1 <= i => p.[i] = zeror.
+ by move=> i ge1_i; apply: gedeg_coeff; rewrite eq1_degp.
exists p.[0]; split; last first.
+ apply/poly_eqP => c /ler_eqVlt -[<<-|]; first by rewrite polyCE.
  by move=> gt0_c; rewrite polyCE gtr_eqF //= &(pC) /#.
apply: contraL eq1_degp => z_p0; suff ->: p = poly0 by rewrite deg0.
apply/poly_eqP=> c; rewrite poly0E => /ler_eqVlt [<<-//|].
by move=> gt0_c; apply: pC => /#.
qed.

lemma lc_eq0 p : (lc p = zeror) <=> (p = poly0).
proof.
case: (p = poly0) => [->|] /=; first by rewrite lc0.
rewrite -deg_eq0 eqr_le ge0_deg /= -ltrNge => gt0_deg.
pose P i := forall j, (i <= j)%Int => p.[j] = zeror.
apply/negP => zp; have := argmin_min idfun P (deg p - 1) _; 1: smt().
move=> @/idfun /= j /ler_eqVlt [<<-//| ltj].
by apply: gedeg_coeff => /#.
qed.

lemma degN p : deg (-p) = deg p.
proof.
rewrite /deg; congr; apply/fun_ext => /= i; apply/eq_iff.
by split=> + j - /(_ j); rewrite polyNE oppr_eq0.
qed.

lemma lcN p : lc (-p) = - lc p.
proof. by rewrite degN polyNE. qed.

lemma degD p q : deg (p + q) <= max (deg p) (deg q).
proof.
apply: deg_leP; [by smt(ge0_deg) | move=> i /ler_maxrP[le1 le2]].
by rewrite polyDE !gedeg_coeff ?addr0.
qed.

lemma degB p q : deg (p - q) <= max (deg p) (deg q).
proof. by rewrite -(degN q) &(degD). qed.

lemma degDl p q : deg q < deg p => deg (p + q) = deg p.
proof.
move=> le_pq; have gt0_p: 0 < deg p.
- by apply/(ler_lt_trans _ _ _ _ le_pq)/ge0_deg.
apply: degP=> //.
- rewrite polyDE (gedeg_coeff q) 1:/#.
  by rewrite addr0 lc_eq0 -deg_eq0 gtr_eqF.
- move=> i le_pi; rewrite polyDE !gedeg_coeff ?addr0 //.
  by apply/ltrW/(ltr_le_trans _ _ _ le_pq).
qed.

lemma lcDl p q : deg q < deg p => lc (p + q) = lc p.
proof.
move=> ^lt_pq /degDl ->; rewrite polyDE.
by rewrite addrC gedeg_coeff ?add0r //#.
qed.

lemma degDr p q : deg p < deg q => deg (p + q) = deg q.
proof. by move/degDl; rewrite addrC. qed.

lemma lcDr p q : deg q < deg p => lc (p + q) = lc p.
proof. by move/lcDl; rewrite addrC. qed.

(* -------------------------------------------------------------------- *)
lemma polyMEw M p q k : (k <= M)%Int => (p * q).[k] =
  BCA.bigi predT (fun i => p.[i] * q.[k-i]) 0 (M+1).
proof.
move=> le_kM; case: (k < 0) => [lt0_k|/lerNgt ge0_k].
+ rewrite lt0_coeff // BCA.big_seq BCA.big1 //= => i.
  by case/mem_range=> [ge0_i lt_iM]; rewrite (lt0_coeff q) ?mulr0 //#.
rewrite (@BCA.big_cat_int (k+1)) 1,2:/# -polyME.
rewrite BCA.big_seq BCA.big1 2:addr0 //= => i /mem_range.
by case=> [lt_ki lt_iM]; rewrite (lt0_coeff q) ?mulr0 //#.
qed.

lemma mulpC : commutative ( * ).
proof.
move=> p q; apply: poly_eqP => k ge0_k; rewrite !polyME.
pose F j := k - j; rewrite (@BCA.big_reindex _ _ F F) 1:/#.
rewrite predT_comp /(\o) /=; pose s := map _ _.
apply: (eq_trans _ _ _ (BCA.eq_big_perm _ _ _ (range 0 (k+1)) _)).
+ rewrite uniq_perm_eq 2:&(range_uniq) /s.
  * rewrite map_inj_in_uniq 2:&(range_uniq) => x y.
    by rewrite !mem_range /F /#.
  * move=> x; split => [/mapP[y []]|]; 1: by rewrite !mem_range /#.
    rewrite !mem_range => *; apply/mapP; exists (F x).
    by rewrite !mem_range /F /#.
+ by apply: BCA.eq_bigr => /= i @/F; rewrite mulrC /#.
qed.

lemma polyMEwr M p q k : (k <= M)%Int => (p * q).[k] =
  BCA.bigi predT (fun i => p.[k-i] * q.[i]) 0 (M+1).
proof.
rewrite mulpC => /polyMEw ->; apply: BCA.eq_bigr.
by move=> i _ /=; rewrite mulrC.
qed.

lemma polyMEr p q k : (p * q).[k] =
  BCA.bigi predT (fun i => p.[k-i] * q.[i]) 0 (k+1).
proof. by rewrite (@polyMEwr k). qed.

lemma mulpA : associative ( * ).
proof.
move=> p q r; apply: poly_eqP => k ge0_k.
have ->: ((p * q) * r).[k] =
  BCA.bigi predT (fun i =>
    BCA.bigi predT (fun j => p.[j] * q.[k - i - j] * r.[i]) 0 (k+1)
  ) 0 (k+1).
+ rewrite polyMEr !BCA.big_seq &(BCA.eq_bigr) => /= i.
  case/mem_range => ge0_i lt_i_Sk; rewrite (@polyMEw k) 1:/#.
  by rewrite BCA.mulr_suml &(BCA.eq_bigr).
have ->: (p * (q * r)).[k] =
  BCA.bigi predT (fun i =>
    BCA.bigi predT (fun j => p.[i] * q.[k - i - j] * r.[j]) 0 (k+1)
  ) 0 (k+1).
+ rewrite polyME !BCA.big_seq &(BCA.eq_bigr) => /= i.
  case/mem_range => g0_i lt_i_Sk; rewrite (@polyMEwr k) 1:/#.
  by rewrite BCA.mulr_sumr &(BCA.eq_bigr) => /= j; rewrite mulrA.
rewrite BCA.exchange_big &(BCA.eq_bigr) => /= i.
by rewrite &(BCA.eq_bigr) => /= j /#.
qed.

lemma mul1p : left_id poly1 polyM.
proof.
move=> p; apply: poly_eqP => c ge0_c.
rewrite polyME BCA.big_int_recl //= polyCE /= mul1r.
rewrite BCA.big_seq BCA.big1 -1:?addr0 //=.
move=> i; rewrite mem_range=> -[ge0_i _]; rewrite polyCE.
by rewrite addz1_neq0 //= mul0r.
qed.

lemma mul0p : left_zero poly0 polyM.
proof.
move=> p; apply/poly_eqP=> c _; rewrite poly0E polyME.
by rewrite BCA.big1 //= => i; rewrite poly0E mul0r.
qed.

lemma mulpDl: left_distributive polyM polyD.
proof.
move=> p q r; apply: poly_eqP => c ge0_c; rewrite !(polyME, polyDE).
by rewrite -BCA.big_split &(BCA.eq_bigr) => /= i; rewrite polyDE mulrDl.
qed.

lemma onep_neq0 : poly1 <> poly0.
proof. by apply/negP => /poly_eqP /(_ 0); rewrite !polyCE /= oner_neq0. qed.

clone export Ring.ComRing as PolyComRing with
  type t      <= poly ,
    op zeror  <= poly0,
    op oner   <= poly1,
    op ( + )  <= polyD,
    op [ - ]  <= polyN,
    op ( * )  <= polyM

  proof addrA     by apply ZPoly.addrA
  proof addrC     by apply ZPoly.addrC
  proof add0r     by apply ZPoly.add0r
  proof addNr     by apply ZPoly.addNr
  proof mulrA     by apply mulpA
  proof mulrC     by apply mulpC
  proof mul1r     by apply mul1p
  proof mulrDl    by apply mulpDl
  proof oner_neq0 by apply onep_neq0

  remove abbrev (-)
  remove abbrev (/).

(* -------------------------------------------------------------------- *)
lemma mul_lc p q : lc p * lc q = (p * q).[deg p + deg q - 2].
proof.
case: (p = poly0) => [->|nz_p]; first by rewrite !(mul0r, poly0E).
case: (q = poly0) => [->|nz_q]; first by rewrite !(mulr0, poly0E).
have ->: deg p + deg q - 2 = (deg p - 1) + (deg q - 1) by ring.
pose cp := deg p - 1; pose cq := deg q - 1.
rewrite polyME (BCA.bigD1 _ _ cp) ?range_uniq //=.
- rewrite mem_range subr_ge0 deg_ge1 nz_p /= -addrA.
  by rewrite ltr_addl ltzS /cq subr_ge0 deg_ge1.
rewrite addrAC subrr /= BCA.big_seq_cond BCA.big1 ?addr0 //=.
move=> i [/mem_range [ge0_i lt] @/predC1 nei].
case: (i < deg p) => [lt_ip| /lerNgt le_pi]; last first.
- by rewrite gedeg_coeff // mul0r.
by rewrite (gedeg_coeff q) ?mulr0 //#.
qed.

(* -------------------------------------------------------------------- *)
lemma degM_le p q : p <> poly0 => q <> poly0 =>
  deg (p * q) + 1 <= deg p + deg q.
proof.
move=> nz_p nz_q; rewrite addrC -ler_subr_addl &(deg_leP).
- by move: nz_p nz_q; rewrite -!deg_eq0 !eqr_le !ge0_deg /= -!ltrNge /#.
move=> i lei; rewrite polyME BCA.big_seq BCA.big1 //=.
move=> j /mem_range [ge0_j /ltzS le_ij].
case: (j < deg p) => [lt_jp|/lerNgt le_pk].
- by rewrite mulrC gedeg_coeff ?mul0r //#.
- by rewrite gedeg_coeff ?mul0r //#.
qed.

(* -------------------------------------------------------------------- *)
lemma degM_proper p q :
  lc p * lc q <> Coeff.zeror => deg (p * q) = (deg p + deg q) - 1.
proof.
case: (p = poly0) => [->|nz_p]; first by rewrite lc0 !mul0r.
case: (q = poly0) => [->|nz_q]; first by rewrite lc0 !mulr0.
move=> nz_lc; apply/(IntID.addIr 1); rewrite -!addrA /=.
apply: contraR nz_lc; rewrite eqr_le degM_le //=.
by rewrite lerNgt /= => lt_pq; rewrite mul_lc gedeg_coeff //#.
qed.

(* -------------------------------------------------------------------- *)
lemma lcM_proper p q :
  lc p * lc q <> Coeff.zeror => lc (p * q) = lc p * lc q.
proof. by move=> reg; rewrite degM_proper //= -mul_lc. qed.

(* -------------------------------------------------------------------- *)
lemma degZ_le c p : deg (c ** p) <= deg p.
proof.
case: (c = Coeff.zeror) => [->|nz_c]; 1: by rewrite scale0p deg0 ge0_deg.
case: (p = poly0) => [->|nz_p]; 1: by rewrite scalep0 deg0.
have nz_cp : polyC c <> poly0.
- by apply/negP => /(congr1 deg); rewrite deg0 degC nz_c.
rewrite scalepE -(ler_add2r 1); move/ler_trans: (degM_le _ _ nz_cp nz_p).
by apply; rewrite degC nz_c /= addrC.
qed.

(* -------------------------------------------------------------------- *)
lemma degZ_lreg c p : Coeff.lreg c => deg (c ** p) = deg p.
proof.
case: (p = poly0) => [->|^nz_p]; 1: by rewrite scalep0 deg0.
rewrite -deg_gt0 => gt0_dp lreg_c; apply/degP => // => [|i gei].
- by rewrite polyZE Coeff.mulrI_eq0 // lc_eq0.
- by rewrite gedeg_coeff // &(ler_trans (deg p)) // &(degZ_le).
qed.

(* -------------------------------------------------------------------- *)
lemma lcZ_lreg c p : Coeff.lreg c => lc (c ** p) = c * lc p.
proof. by move=> reg_c; rewrite degZ_lreg // polyZE. qed.

(* -------------------------------------------------------------------- *)
lemma lreg_lc p : lreg (lc p) => lreg p.
proof.
move/Coeff.mulrI_eq0=> reg_p; apply/mulrI0_lreg => q.
apply: contraLR=> nz_q; rewrite -lc_eq0.
by rewrite lcM_proper reg_p lc_eq0.
qed.

(* -------------------------------------------------------------------- *)
lemma degXn_le (p : poly) i :
  p <> poly0 => 0 <= i => deg (exp p i) <= i * (deg p - 1) + 1.
proof.
move=> nz_p; elim: i => [|i ge0_i ih]; first by rewrite !expr0 deg1.
rewrite exprS // mulrDl /= addrAC !addrA ler_subr_addl (IntID.addrC 1).
case: (exp p i = poly0) => [->|nz_pX].
- by rewrite mulr0 deg0 /=; rewrite -deg_gt0 in nz_p => /#.
apply: (ler_trans (deg p + deg (exp p i))); 1: by apply: degM_le.
by rewrite addrC &(ler_add2r).
qed.

(* -------------------------------------------------------------------- *)
lemma degXn_proper (p : poly) i :
  lreg (lc p) => 0 <= i => deg (exp p i) = i * (deg p - 1) + 1.
proof.
move=> lreg_p; elim: i => [|i ge0_i ih]; first by rewrite expr0 deg1.
rewrite exprS // degM_proper; last by rewrite ih #ring.
by rewrite mulrI_eq0 // lc_eq0 lreg_neq0 // &(lregXn) // &(lreg_lc).
qed.

(* -------------------------------------------------------------------- *)
lemma deg_polyXn i : 0 <= i => deg (exp X i) = i + 1.
proof.
move=> ge0_i; rewrite degXn_proper //.
- by rewrite lcX &(Coeff.lreg1).
- by rewrite degX #ring.
qed.

(* -------------------------------------------------------------------- *)
lemma lcXn_proper (p : poly) i :
  lreg (lc p) => 0 <= i => lc (exp p i) = exp (lc p) i.
proof.
move=> reg_p; elim: i => [|i ge0_i ih]; 1: by rewrite !expr0 lc1.
rewrite !exprS // degM_proper /=; last by rewrite -mul_lc ih.
by rewrite mulrI_eq0 // lreg_neq0 // ih lregXn.
qed.

(* -------------------------------------------------------------------- *)
lemma lc_polyXn i : 0 <= i => lc (exp X i) = Coeff.oner.
proof.
move=> ge0_0; rewrite lcXn_proper ?lcX //.
- by apply: Coeff.lreg1. - by rewrite expr1z.
qed.

(* -------------------------------------------------------------------- *)
lemma polyCX c i : 0 <= i => exp (polyC c) i = polyC (exp c i).
proof.
elim: i => [|i ge0_i ih]; first by rewrite !expr0.
by rewrite !exprS // ih polyCM.
qed.

(* -------------------------------------------------------------------- *)
lemma deg_polyXnDC i c : 0 < i => deg (exp X i + polyC c) = i + 1.
proof. by move=> ge0_i; rewrite degDl 1?degC deg_polyXn 1:ltrW //#. qed.

(* -------------------------------------------------------------------- *)
lemma lc_polyXnDC i c : 0 < i => lc (exp X i + polyC c) = Coeff.oner.
proof.
move=> gti_0; rewrite lcDl ?lc_polyXn // -1:ltrW //.
by rewrite degC deg_polyXn 1:ltrW //#.
qed.

(* -------------------------------------------------------------------- *)
lemma polyXnE i k :
  0 <= i => (exp X i).[k] = if k = i then Coeff.oner else Coeff.zeror.
proof.
move=> ge0_i; elim: i ge0_i k => [|i ge0_i ih] k.
- by rewrite expr0 polyCE.
- by rewrite exprS // (PolyComRing.mulrC) polyMXE ih /#.
qed.

(* -------------------------------------------------------------------- *)
theory BigPoly.
clone include BigComRing with theory CR <- PolyComRing

  remove abbrev CR.(-)
  remove abbrev CR.(/) 

  rename [theory] "BAdd" as "PCA"
         [theory] "BMul" as "PCM".

lemma polysumE ['a] P F s k :
  (PCA.big<:'a> P F s).[k] = BCA.big P (fun i => (F i).[k]) s.
proof.
elim: s => /= [|x s ih]; first by rewrite poly0E.
rewrite !BCA.big_cons -ih PCA.big_cons /=.
by rewrite -polyDE -(fun_if (fun q => q.[k])).
qed.

lemma polyE (p : poly) :
  p = PCA.bigi predT (fun i => p.[i] ** exp X i) 0 (deg p).
proof.
apply/poly_eqP=> c ge0_c; rewrite polysumE /=; case: (c < deg p).
- move=> lt_c_dp; rewrite (BCA.bigD1 _ _ c) ?(mem_range, range_uniq) //=.
  rewrite !(coeffpE, polyXnE) //= mulr1 BCA.big1_seq ?addr0 //=.
  move=> @/predC1 i [ne_ic /mem_range [ge0_i _]].
  by rewrite !(coeffpE, polyXnE) // (eq_sym c i) ne_ic /= mulr0.
- move=> /lerNgt ge_c_dp; rewrite gedeg_coeff //.
  rewrite BCA.big_seq BCA.big1 //= => i /mem_range [ge0_i lt_i].
  by rewrite !(coeffpE, polyXnE) // (_ : c <> i) ?mulr0 //#.
qed.

lemma polywE n (p : poly) : deg p <= n =>
  p = PCA.bigi predT (fun i => p.[i] ** exp X i) 0 n.
proof.
move=> le_pn; rewrite (PCA.big_cat_int (deg p)) // ?ge0_deg.
rewrite {1}polyE; pose c := PCA.big _ _ _.
pose d := PCA.big _ _ _; suff ->: d = poly0 by rewrite addr0.
rewrite /d PCA.big_seq PCA.big1 => //= i /mem_range [gei _].
by rewrite gedeg_coeff // scale0p.
qed.

lemma deg_sum ['a] P F r c :
     0 <= c
  => (forall x, P x => deg (F x) <= c)
  => deg (PCA.big<:'a> P F r) <= c.
proof.
move=> ge0_c le; elim: r => [|x r ih]; 1: by rewrite PCA.big_nil deg0.
rewrite PCA.big_cons; case: (P x) => // Px.
by rewrite &(ler_trans _ _ _ (degD _ _)) ler_maxrP ih le.
qed.
end BigPoly.

import BigPoly.

(* -------------------------------------------------------------------- *)
clone import IdealComRing as PIdeal with
    type t               <- poly,
  theory IComRing        <- PolyComRing,
      op BigDom.BAdd.big <- BigPoly.PCA.big<:'a>,
      op BigDom.BMul.big <- BigPoly.PCM.big<:'a>

  remove abbrev BigDom.BAdd.bigi
  remove abbrev BigDom.BMul.bigi.

(* -------------------------------------------------------------------- *)
op peval (p : poly) (a : coeff) =
  BCA.bigi predT (fun i => p.[i] * exp a i) 0 (deg p + 1).

(* -------------------------------------------------------------------- *)
abbrev root p a = peval p a = Coeff.zeror.

(* -------------------------------------------------------------------- *)
lemma peval_degE p a :
  peval p a = BCA.bigi predT (fun i => p.[i] * exp a i) 0 (deg p).
proof.
rewrite /peval (BCA.big_cat_int (deg p)) ?ge0_deg // 1:/#.
by rewrite BCA.big_int1 /= gedeg_coeff // mul0r addr0.
qed.

lemma pevalwE n p a : deg p <= n =>
  peval p a = BCA.bigi predT (fun i => p.[i] * exp a i) 0 n.
proof.
move=> le_pn; rewrite peval_degE (BCA.big_cat_int (deg p) 0 n) ?ge0_deg //.
rewrite (BCA.big1_seq _ _ (range (deg p) n)) ?addr0 //=.
by move=> i /mem_range [le_pi _]; rewrite gedeg_coeff // mul0r.
qed.

(* -------------------------------------------------------------------- *)
lemma pevalC c a : peval (polyC c) a = c.
proof.
by rewrite (pevalwE 1) ?degC_le // BCA.big_int1 /= polyCE /= expr0 mulr1.
qed.

lemma peval0 a : peval poly0 a = Coeff.zeror.
proof. by apply: pevalC. qed.

lemma peval1 a : peval poly1 a = Coeff.oner.
proof. by apply: pevalC. qed.

lemma pevalX a : peval X a = a.
proof.
rewrite peval_degE degX (BCA.big_cat_int 1) // !BCA.big_int1 /=.
by rewrite !polyXE /= mul0r add0r expr1 mul1r.
qed.

(* -------------------------------------------------------------------- *)
lemma pevalD p q a : peval (p + q) a = peval p a + peval q a.
proof.
pose n := max (deg p) (deg q); rewrite (pevalwE n (p + q)) 1:degD //.
rewrite (pevalwE n p) 1:/# (pevalwE n q) 1:/# BCA.sumrD.
by apply: BCA.eq_bigr => i _ /=; rewrite polyDE mulrDl.
qed.

lemma pevalN p a : peval (-p) a = - peval p a.
proof.
rewrite /peval degN BCA.sumrN; apply: BCA.eq_bigr => i _ /=.
by rewrite polyNE mulNr.
qed.

lemma pevalB p q a : peval (p - q) a = peval p a - peval q a.
proof. by rewrite pevalD pevalN. qed.

lemma pevalZ c p a : peval (c ** p) a = c * peval p a.
proof.
rewrite (pevalwE (deg p)) 1:degZ_le peval_degE BCA.mulr_sumr.
by apply: BCA.eq_bigr => i _ /=; rewrite polyZE mulrA.
qed.

lemma peval_sum ['a] P F s a :
  peval (PCA.big<:'a> P F s) a = BCA.big P (fun x => peval (F x) a) s.
proof.
elim: s => [|x s ih]; first by rewrite PCA.big_nil BCA.big_nil peval0.
by rewrite PCA.big_cons BCA.big_cons; case: (P x); rewrite ?pevalD ih.
qed.

(* -------------------------------------------------------------------- *)
lemma pevalMX p a : peval (p * X) a = peval p a * a.
proof.
rewrite (pevalwE (deg p + 1)).
- apply: deg_leP => [|i le_i]; first by rewrite ler_paddl // ge0_deg.
  by rewrite polyMXE gedeg_coeff //#.
rewrite BCA.big_int_recl ?ge0_deg //= polyMXE lt0_coeff //= mul0r add0r.
rewrite peval_degE BCA.mulr_suml !BCA.big_seq &(BCA.eq_bigr) /=.
by move=> i /mem_range [ge0_i _]; rewrite polyMXE /= exprSr // mulrA.
qed.

lemma pevalMXn p a i : 0 <= i => peval (p * exp X i) a = peval p a * exp a i.
proof.
elim: i => [|i ge0_i ih]; first by rewrite !expr0 mulr1 Coeff.mulr1.
by rewrite exprSr // mulrA pevalMX ih exprSr // mulrA.
qed.

lemma pevalXn a i : 0 <= i => peval (exp X i) a = exp a i.
proof.
by move=> ge0_i; rewrite -(mul1r (exp X i)) pevalMXn // peval1 mul1r.
qed.

lemma pevalM p q a : peval (p * q) a = peval p a * peval q a.
proof.
rewrite {1}(polyE q) PCA.mulr_sumr peval_sum (peval_degE q) BCA.mulr_sumr.
rewrite !BCA.big_seq &(BCA.eq_bigr) => i /mem_range [ge0_i _] /=.
by rewrite scalepE mulrCA -scalepE pevalZ pevalMXn // mulrCA.
qed.

lemma peval_exp p a i : 0 <= i => peval (exp p i) a = exp (peval p a) i.
proof.
elim: i => [|i ge0_i ih]; first by rewrite !expr0 peval1.
by rewrite !exprS // pevalM ih.
qed.

lemma pevalXsubC a b : peval (X - polyC a) b = b - a.
proof. by rewrite pevalB pevalX pevalC. qed.

(* -------------------------------------------------------------------- *)
(* Division by (X - a) leaves the remainder peval p a                  *)
lemma peval_factor p a : exists q, p = q * (X - polyC a) + polyC (peval p a).
proof.
have hXn: forall i, 0 <= i =>
  exists q, exp X i = (X - polyC a) * q + polyC (exp a i).
- elim=> [|i ge0_i [q qE]]; first by exists poly0; rewrite !expr0 mulr0 add0r.
  exists (X * q + polyC (exp a i)); rewrite exprS // qE Coeff.exprS // polyCM.
  by rewrite !mulrDr -addrA -mulrDl subrK mulrCA.
have: forall s, (forall i, i \in s => 0 <= i) => exists q,
  PCA.big predT (fun i => p.[i] ** exp X i) s
  = (X - polyC a) * q + polyC (BCA.big predT (fun i => p.[i] * exp a i) s).
- elim=> [|i s ih] hs.
  - by exists poly0; rewrite PCA.big_nil BCA.big_nil mulr0 add0r.
  case: (ih _) => [j js|q qE]; first by apply: hs; rewrite /= js.
  case: (hXn i _) => [|r rE]; first by apply: hs.
  exists (p.[i] ** r + q); rewrite PCA.big_cons BCA.big_cons /= qE rE polyCD.
  by rewrite scalepDr !scalepE polyCM mulrDr mulrCA addrACA.
move/(_ (range 0 (deg p)) _); first by move=> i /mem_range [].
by case=> q qE; exists q; rewrite peval_degE (mulrC q) -qE -polyE.
qed.

(* -------------------------------------------------------------------- *)
lemma root0 x : root poly0 x.
proof. by rewrite peval0. qed.

lemma rootC c x : root (polyC c) x <=> c = Coeff.zeror.
proof. by rewrite pevalC. qed.

lemma rootX x : root X x <=> x = Coeff.zeror.
proof. by rewrite pevalX. qed.

lemma rootN p x : root (-p) x <=> root p x.
proof. by rewrite pevalN oppr_eq0. qed.

lemma root_XsubC a x : root (X - polyC a) x <=> x = a.
proof. by rewrite pevalXsubC subr_eq0. qed.

(* -------------------------------------------------------------------- *)
lemma factor_theorem p a : root p a <=> exists q, p = q * (X - polyC a).
proof.
split=> [rt|[q ->]]; last by rewrite pevalM pevalXsubC subrr mulr0.
by case: (peval_factor p a) => q; rewrite rt addr0 => qE; exists q.
qed.

lemma root_factor_theorem p a : root p a <=> (X - polyC a) %| p.
proof. by rewrite factor_theorem dvdrP. qed.

(* -------------------------------------------------------------------- *)
op prepolyL (a : coeff list) = fun i => nth Coeff.zeror a i.

lemma isprepolyL a : ispoly (prepolyL a).
proof.
split=> [c lt0_c|]; first by rewrite /prepolyL nth_neg.
exists (size a) => c gtc; rewrite /prepolyL nth_out //.
by apply/negP => -[_]; rewrite ltrNge /= ltrW.
qed.

op polyL a = to_polyd (prepolyL a).

lemma polyLE a c : (polyL a).[c] = nth Coeff.zeror a c.
proof. by rewrite coeffE 1:isprepolyL. qed.

lemma degL_le a : deg (polyL a) <= size a.
proof.
apply: deg_leP; first exact: size_ge0.
by move=> i gei; rewrite polyLE nth_out //#.
qed.

lemma degL a :
  last Coeff.zeror a <> Coeff.zeror => deg (polyL a) = size a.
proof.
move=> nz; apply/degP.
- by case: a nz => //= x a _; rewrite addrC ltzS size_ge0.
- by rewrite polyLE nth_last.
- move=> i sza; rewrite gedeg_coeff //.
  by apply: (ler_trans (size a)) => //; apply: degL_le.
qed.

lemma inj_polyL a1 a2 :
  size a1 = size a2 => polyL a1 = polyL a2 => a1 = a2.
proof.
move=> eq_sz /poly_eqP eq; apply: (eq_from_nth Coeff.zeror)=> //.
by move=> i [+ _] - /eq; rewrite !polyLE.
qed.

lemma surj_polyL p n :
  deg p <= n => exists s, size s = n /\ p = polyL s.
proof.
move=> len; exists (map (fun i => p.[i]) (range 0 n)); split.
- by rewrite size_map size_range /=; smt(ge0_deg).
apply/poly_eqP=> c ge0_c; rewrite polyLE; case: (c < n).
- by move=> lt_cn; rewrite (nth_map 0) ?size_range ?nth_range //#.
- rewrite ltrNge /= => le_nc; rewrite gedeg_coeff // 1:/#.
  by rewrite nth_out // size_map size_range /#.
qed.

(* -------------------------------------------------------------------- *)
lemma finite_for_poly_ledeg n p s :
     is_finite_for p s
  => is_finite_for
       (fun q => deg q <= max 0 n /\ (forall i, 0 <= i < n => p q.[i]))
       (map polyL (alltuples n s)).
proof.
move=> ^[uq hmem] /finite_for_list /(_ n) [usq hmems]; split.
- rewrite map_inj_in_uniq // => xs ys
    /alltuplesP [szxs memxs] /alltuplesP [szys memys].
  by apply: inj_polyL; rewrite szxs szys.
move=> q; split=> [/mapP[xs [/alltuplesP [szxs memxs ->]]]|].
- rewrite (ler_trans (size xs)) ?szxs //= => [|i [ge0_i lei]].
  - by rewrite -szxs; apply: degL_le.
  - by rewrite polyLE &(all_nthP) -1:/#; move/(eq_all _ _ _ hmem): memxs.
case=> ledeg memp; apply/mapP; pose xs :=  map (fun i => q.[i]) (range 0 n).
exists xs; split; first (apply/alltuplesP; split).
- by rewrite size_map size_range.
- apply/(all_nthP _ _ Coeff.zeror) => i [ge0_i +]; rewrite hmem.
  rewrite size_map size_range /= => lei.
  move/(_ i _): memp; first (split=> // _; 1: move=> /#).
  by rewrite (nth_map 0) ?size_range //= nth_range //#.
- apply/poly_eqP=> c ge0_c; rewrite polyLE; case: (c < n).
  - move=> lt_cn; rewrite (nth_map 0) ?size_range ?nth_range //#.
  - rewrite ltrNge /= => le_nc; rewrite gedeg_coeff // 1:/#.
  by rewrite nth_out // size_map size_range /#.
qed.

(* -------------------------------------------------------------------- *)
op dpoly (n : int) (d : coeff distr) =
  dmap (dlist d n) polyL.

lemma supp_dpoly n d p : 0 <= n =>
      p \in dpoly n d
  <=> (deg p <= n /\ forall i, 0 <= i < n => p.[i] \in d).
proof. move=> ge0_n; split.
- case/supp_dmap=> xs [/(supp_dlist _ _ _ ge0_n)].
  case=> ^szxs <- /allP hcf ->; rewrite degL_le /=.
  by move=> i [ge0_i lei]; rewrite polyLE; apply/hcf/mem_nth.
- case=> degp hcf; apply/supp_dmap; case: (surj_polyL _ _ degp).  
  move=> xs [^szxs <- ^pE ->]; exists xs => //=; apply/supp_dlist => /=.
  - by apply/size_ge0.
  apply/allP=> c ^c_in_xs /(nth_index Coeff.zeror) <-.
  rewrite -polyLE -pE; apply/hcf; rewrite index_ge0 /=.
  by rewrite -szxs index_mem c_in_xs.
qed.

(* -------------------------------------------------------------------- *)
lemma dpoly_ll n d : is_lossless d => is_lossless (dpoly n d).
proof. by move=> d_ll; apply/dmap_ll/dlist_ll. qed.

(* -------------------------------------------------------------------- *)
lemma dpoly_fu n d : 0 <= n => is_full d =>
  forall (p : poly), deg p <= n => p \in dpoly n d.
proof.
move=> ge0_n d_fu p /surj_polyL[xs [szxs ->>]].
apply/dmap_supp/supp_dlist => //; rewrite szxs /=.
by apply/allP=> x _; apply/d_fu.
qed.

(* -------------------------------------------------------------------- *)
lemma dpoly_uni n d : 0 <= n => is_uniform d => is_uniform (dpoly n d).
proof.
move=> ge0_n d_uni; apply/dmap_uni_in_inj/dlist_uni/d_uni.
by move=> xs ys xs_d ys_d; rewrite &(inj_polyL) !(supp_dlist_size d n).
qed.
end PolyComRing.

(* ==================================================================== *)
abstract theory Poly.
type coeff.

clone import IDomain as IDCoeff with type t <= coeff.

clone include PolyComRing with
  type coeff   <- coeff,
  theory Coeff <- IDCoeff,
  op PolyComRing.invr (p : poly) =
    (if deg p = 1 then polyC (IDCoeff.invr p.[0]) else p).

clear [PolyComRing.* PolyComRing.AddMonoid.* PolyComRing.MulMonoid.*].

import BigCf.

(* -------------------------------------------------------------------- *)
lemma degM p q : p <> poly0 => q <> poly0 =>
  deg (polyM p q) = deg p + deg q - 1.
proof.
rewrite -!lc_eq0 -!lregP => reg_p reg_q.
by rewrite &(degM_proper) mulf_eq0 negb_or -!lregP.
qed.

(* -------------------------------------------------------------------- *)
pred unitp (p : poly) =
  deg p = 1 /\ IDCoeff.unit p.[0].

(* -------------------------------------------------------------------- *)
op polyV (p : poly) =
  if deg p = 1 then polyC (IDCoeff.invr p.[0]) else p.

(* -------------------------------------------------------------------- *)
clone import Ring.IDomain as IDPoly with
  type t      <- poly ,
    op zeror  <- poly0,
    op oner   <- poly1,
    op ( + )  <- polyD,
    op [ - ]  <- polyN,
    op ( * )  <- polyM,
    op invr   <- polyV,
    op exp    <- PolyComRing.exp,
  pred unit   <- unitp

  proof *

  remove abbrev (-)
  remove abbrev (/).

realize addrA     by apply PolyComRing.addrA    .
realize addrC     by apply PolyComRing.addrC    .
realize add0r     by apply PolyComRing.add0r    .
realize addNr     by apply PolyComRing.addNr    .
realize mulrA     by apply PolyComRing.mulrA    .
realize mulrC     by apply PolyComRing.mulrC    .
realize mul1r     by apply PolyComRing.mul1r    .
realize mulrDl    by apply PolyComRing.mulrDl   .
realize oner_neq0 by apply PolyComRing.oner_neq0.

(* -------------------------------------------------------------------- *)
realize mulVr.
proof.
move=> p inv_p; apply/poly_eqP=> c /ler_eqVlt [<<-|].
+ rewrite polyCE /= polyME /= BCA.big_int1 /= /polyV.
  by case: inv_p => -> inv_p0 /=; rewrite polyCE /= mulVr.
+ move=> gt0_c; rewrite polyME polyCE gtr_eqF //=.
  rewrite BCA.big_seq BCA.big1 //= => i; rewrite mem_range.
  case: inv_p => @/polyV ^ degp -> inv_p0 [+ lt_i_Sc] - /ler_eqVlt [<<-|] /=.
  - by rewrite (gedeg_coeff _ c) -1:mulr0 // degp /#.
  - move=> gt0_i; rewrite (gedeg_coeff _ i) -1:mul0r //.
    by apply/(ler_trans _ _ _ (degC_le _)) => /#.
qed.

(* -------------------------------------------------------------------- *)
realize unitout.
proof.
move=> p @/unitp @/polyV; case: (deg p = 1) => //=.
move=> dp_eq1 unitN_p0; apply/poly_eqP => c ge0_c.
case: (c < 1) => [lt1_c|/lerNgt ge1_c]; last first.
- rewrite !(@gedeg_coeff _ c) 2:dp_eq1 //.
  by apply/(ler_trans _ _ _ _ ge1_c)/degC_le.
- suff ->: c = 0 by rewrite polyCE /= invr_out.
  by rewrite eqr_le ge0_c /= -ltz1.
qed.

(* -------------------------------------------------------------------- *)
realize unitP.
proof.
move=> p q ^pMqE /(congr1 deg); rewrite deg1.
move/(congr1 ((+) 1)) => /=; rewrite addrC; move: pMqE.
case: (deg p = 0) => [/deg_eq0->|nz_p].
- by rewrite mulpC mul0p eq_sym onep_neq0.
case: (deg q = 0) => [/deg_eq0->|nz_q].
- by rewrite mul0p eq_sym onep_neq0.
rewrite degM -1?deg_eq0 // => ME eq.
have {eq}[]: deg p = 1 /\ deg q = 1 by smt(ge0_deg).
move/deg_eq1=> [cp [nz_cp ->>]]; move/deg_eq1=> [cq [nz_cq ->>]].
move/poly_eqP: ME => /(_ 0 _) //; rewrite polyCE /=.
rewrite polyME BCA.big_int1 /= => /IDCoeff.unitP @/unitp -> /=.
by rewrite deg_eq1; exists cp.
qed.

(* -------------------------------------------------------------------- *)
realize mulf_eq0.
proof.
move=> p q; split=> [|[] ->]; last 2 by rewrite (mulr0, mul0r).
apply: contraLR; rewrite negb_or => -[nz_p nz_q]; apply/negP.
move/(congr1 (fun p => deg p + 1)) => /=; rewrite  deg0 degM //=.
by rewrite gtr_eqF // -lez_add1r ler_add deg_ge1.
qed.

(* -------------------------------------------------------------------- *)
lemma lcM (p q : poly) : lc (p * q) = lc p * lc q.
proof.
case: (p = poly0) => [->|nz_p]; first by rewrite !(mul0r, lc0).
case: (q = poly0) => [->|nz_q]; first by rewrite !(mulr0, lc0).
by rewrite lcM_proper // mulf_eq0 !lc_eq0 !(nz_p, nz_q).
qed.

(* -------------------------------------------------------------------- *)
lemma degV (p : poly) : deg (polyV p) = deg p.
proof.
rewrite /polyV; case: (deg p = 1); last done.
by case/deg_eq1=> c [nz_c ->>]; rewrite !degC polyCE /= invr_eq0.
qed.

(* -------------------------------------------------------------------- *)
lemma deg_XsubC a : deg (X - polyC a) = 2.
proof. by rewrite degDl ?degX // degN degC; case: (a = IDCoeff.zeror). qed.

lemma rootM p q x : root (p * q) x <=> root p x \/ root q x.
proof. by rewrite pevalM mulf_eq0. qed.

lemma rootZ c p x : c <> IDCoeff.zeror => root (c ** p) x <=> root p x.
proof. by move=> nz_c; rewrite pevalZ mulf_eq0 nz_c. qed.

lemma factor_theorem_deg p a : p <> poly0 => root p a =>
  exists q, deg q = deg p - 1 /\ p = q * (X - polyC a).
proof.
move=> nz_p /factor_theorem [q ->>]; exists q => /=.
have nz_q: q <> poly0 by apply: contra nz_p => ->; rewrite mul0r.
by rewrite degM // -?deg_eq0 deg_XsubC //; ring.
qed.

(* -------------------------------------------------------------------- *)
(* A non-zero polynomial has finitely many roots, less than its degree *)
lemma roots_finite p : p <> poly0 =>
  exists rs, uniq rs /\ size rs < deg p /\ forall x, root p x <=> x \in rs.
proof.
have: forall n, 0 <= n => forall p, p <> poly0 => deg p <= n =>
  exists rs, uniq rs /\ size rs < deg p /\ forall x, root p x <=> x \in rs.
- elim=> [|n ge0_n ih] q nz_q le_qn.
  - by move: le_qn; rewrite lerNgt deg_gt0 nz_q.
  case: (exists x, root q x) => [[x rx]|nrq]; last first.
  - exists []; rewrite /= deg_gt0 nz_q /= => y; apply/negP => ry.
    by apply: nrq; exists y.
  case: (factor_theorem_deg q x nz_q rx) => r [degr ->>].
  have nz_r: r <> poly0 by apply: contra nz_q => ->; rewrite mul0r.
  case: (ih r nz_r _) => [/#|rs [_ [sz_rs hrs]]].
  exists (undup (x :: rs)); split; first by apply: undup_uniq.
  split=> [|y]; last by rewrite mem_undup /= -hrs rootM root_XsubC orbC.
  by apply: (ler_lt_trans (size (x :: rs))) => [|/#]; apply: size_undup.
by move=> h nz_p; apply: (h (deg p)) => //; apply: ge0_deg.
qed.

lemma max_poly_roots p rs :
  p <> poly0 => all (root p) rs => uniq rs => size rs < deg p.
proof.
move=> nz_p /allP rts uq_rs; case: (roots_finite p nz_p) => s [_ [sz hs]].
apply: (ler_lt_trans _ _ _ _ sz); apply: uniq_leq_size => // x /rts /=.
by rewrite hs.
qed.

(* -------------------------------------------------------------------- *)
lemma mu_root_le (d : coeff distr) p m :
     p <> poly0
  => (forall x, mu1 d x <= m)
  => mu d (root p) <= (deg p - 1)%r * m.
proof.
move=> nz_p le_m; case: (roots_finite p nz_p) => rs [_ [sz hrs]].
rewrite (mu_eq d _ (mem rs)) => [x /=|]; first by rewrite hrs.
apply: (RealOrder.ler_trans _ _ _ (mu_mem_le_mu1 d rs m le_m)).
apply: RealOrder.ler_wpmul2r; last by rewrite le_fromint /#.
by apply: (RealOrder.ler_trans _ _ _ (ge0_mu d (pred1 witness)) (le_m witness)).
qed.

lemma mu_root_uni (d : coeff distr) p :
     p <> poly0 => is_lossless d => is_uniform d
  => mu d (root p) <= (deg p - 1)%r / (size (to_seq (support d)))%r.
proof.
move=> nz_p d_ll d_uni; apply: mu_root_le => // x.
rewrite mu1_uni_ll // RField.div1r; case: (x \in d) => // _.
by rewrite RealOrder.invr_ge0 le_fromint size_ge0.
qed.
end Poly.
