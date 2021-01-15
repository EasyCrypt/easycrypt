(* -------------------------------------------------------------------- *)
require import AllCore List Ring Bigalg StdBigop StdOrder.
require (*--*) Subtype.
(*---*) import Bigint IntID IntOrder.

(* -------------------------------------------------------------------- *)
abstract theory Poly.
type coeff, poly.

clone import IDomain as Coeff with type t <- coeff.

clone import BigComRing as BigCf with
  type t <- coeff,
  pred CR.unit   <- Coeff.unit,
    op CR.zeror  <- Coeff.zeror,
    op CR.oner   <- Coeff.oner,
    op CR.( + )  <- Coeff.( + ),
    op CR.([-])  <- Coeff.([-]),
    op CR.( * )  <- Coeff.( * ),
    op CR.invr   <- Coeff.invr,
    op CR.intmul <- Coeff.intmul,
    op CR.ofint  <- Coeff.ofint,
    op CR.exp    <- Coeff.exp

    proof CR.*

    rename [theory] "BAdd" as "BCA"
           [theory] "BMul" as "BCM"

    remove abbrev CR.(-)
    remove abbrev CR.(/).

realize CR.addrA     by apply: Coeff.addrA    .
realize CR.addrC     by apply: Coeff.addrC    .
realize CR.add0r     by apply: Coeff.add0r    .
realize CR.addNr     by apply: Coeff.addNr    .
realize CR.oner_neq0 by apply: Coeff.oner_neq0.
realize CR.mulrA     by apply: Coeff.mulrA    .
realize CR.mulrC     by apply: Coeff.mulrC    .
realize CR.mul1r     by apply: Coeff.mul1r    .
realize CR.mulrDl    by apply: Coeff.mulrDl   .
realize CR.mulVr     by apply: Coeff.mulVr    .
realize CR.unitP     by apply: Coeff.unitP    .
realize CR.unitout   by apply: Coeff.unitout  .

(* -------------------------------------------------------------------- *)
type prepoly = int -> coeff.

inductive ispoly (p : prepoly) =
| IsPoly of
      (forall c, c < 0 => p c = zeror)
    & (exists d, forall c, (d < c)%Int => p c = zeror).

clone include Subtype
  with type T   <- prepoly,
       type sT  <- poly,
       pred P   <- ispoly,
         op wsT <- (fun _ => zeror)
  rename "insub" as "to_poly"
  rename "val"   as "of_poly".

(* FIXME: pourquoi un operateur et pas une abbrev *)
op "_.[_]" (p : poly) (i : int) = (of_poly p) i.

lemma lt0_coeff p c : c < 0 => p.[c] = zeror.
proof.
by move=> lt0_c; rewrite /"_.[_]"; case: (of_polyP p) => /(_ _ lt0_c).
qed.

op deg (p : poly) = argmin idfun (fun i => forall j, (i <= j)%Int => p.[j] = zeror).

lemma gedeg_coeff (p : poly) (c : int) : deg p <= c => p.[c] = zeror.
proof.
move=> le_p_c; pose P p i := forall j, (i <= j)%Int => p.[j] = zeror.
case: (of_polyP p) => [wf_p [d hd]]; move: (argminP idfun (P p)).
move/(_ (max (d+1) 0) _ _) => @/P @/idfun /=; first exact: maxrr.
- by move=> j le_d_j; apply: hd => /#.
by apply; apply: le_p_c.
qed.

lemma ge0_deg p : 0 <= deg p.
proof. rewrite /deg &(ge0_argmin). qed.

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
rewrite mem_range => -[gt0_i lt_ic]; rewrite mulf_eq0.
case: (p.[i] = zeror) => //=; apply: contraR.
move/(contra _ _ (gedeg_coeff _ _))/ltrNge => gt_q.
by apply: gedeg_coeff => /#.
qed.

lemma ispolyZ z p : ispoly (prepolyZ z p).
proof.
split => @/prepolyZ [c lt0_c|]; 1: by rewrite mulf_eq0 lt0_coeff.
by exists (deg p + 1) => c gtc; rewrite mulf_eq0 gedeg_coeff /#.
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
abbrev ( - )  = fun p q => p + (-q).
abbrev ( * )  = polyM.
abbrev ( ** ) = polyZ.

(* -------------------------------------------------------------------- *)
lemma coeffE p k : ispoly p => (to_polyd p).[k] = p k.
proof. by move=> ?; rewrite /"_.[_]" to_polydK. qed.

lemma polyCE c k : (polyC c).[k] = if k = 0 then c else zeror.
proof. by rewrite coeffE 1:ispolyC. qed.

lemma poly0E k : poly0.[k] = zeror.
proof. by rewrite polyCE if_same. qed.

lemma polyNE p k : (-p).[k] = - p.[k].
proof. by rewrite coeffE 1:ispolyN. qed.

lemma polyDE p q k : (p + q).[k] = p.[k] + q.[k].
proof. by rewrite coeffE 1:ispolyD. qed.

lemma polyME p q k : (p * q).[k] =
  BCA.bigi predT (fun i => p.[i] * q.[k-i]) 0 (k+1).
proof. by rewrite coeffE 1:ispolyM. qed.

lemma polyZE z p k : (z ** p).[k] = z * p.[k].
proof. by rewrite coeffE 1:ispolyZ. qed.

hint rewrite coeffpE : poly0E polyDE polyNE polyME polyZE.

(* -------------------------------------------------------------------- *)
lemma degP p c :
     0 < c
  => p.[c-1] <> zeror
  => (forall i, c <= i => p.[i] = zeror)
  => deg p = c.
proof.
move=> ge0_c nz_p_cB1 degc @/deg; apply: argmin_eq => @/idfun /=.
- by apply/ltrW. - by apply: degc.
move=> j [ge0_j lt_jc]; rewrite negb_forall /=.
by exists (c-1); apply/negP => /(_ _); first by move=> /#.
qed.

(* -------------------------------------------------------------------- *)
lemma degC c : deg (polyC c) = if c = zeror then 0 else 1.
proof.
case: (c = zeror) => [->|nz_c]; last first.
- apply: degP => //=; first by rewrite polyCE.
  by move=> i ge1_i; rewrite polyCE gtr_eqF //#.
rewrite /deg; apply: argmin_eq => @/idfun //=.
- by move=> j _; rewrite poly0E.
- by move=> j; apply: contraL => _ /#.
qed.

lemma degC_le c : deg (polyC c) <= 1.
proof. by rewrite degC; case: (c = zeror). qed.

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

lemma coeff_degB1_neq0 p : p <> poly0 => p.[deg p - 1] <> zeror.
proof.
rewrite -deg_eq0 eqr_le ge0_deg /= -ltrNge => gt0_deg.
pose P i := forall j, (i <= j)%Int => p.[j] = zeror.
apply/negP => zp; have := argmin_min idfun P (deg p - 1) _; 1: smt().
move=> @/idfun /= j /ler_eqVlt [<<-//| ltj].
by apply: gedeg_coeff => /#.
qed.

lemma degM p q : p <> poly0 => q <> poly0 =>
  deg (polyM p q) + 1 = deg p + deg q.
proof.
move=> nz_p nz_q; apply: (@IntID.addIr (-1)) => /=; apply: degP => /=.
- by move: nz_p nz_q; rewrite -!deg_eq0 !eqr_le !ge0_deg /= -!ltrNge /#.
- rewrite polyME (BCA.bigD1 _ _ (deg p - 1)) ?range_uniq //=.
  - rewrite mem_range ler_subr_addl /= -addrA ltr_add2l ltr_addr.
    rewrite ltr_neqAle ge0_deg /= (eq_sym 0) deg_eq0 nz_q /=.
    by rewrite -(ltzE 0) ltr_neqAle ge0_deg /= eq_sym deg_eq0.
  - have ->: deg p + deg q - 2 - (deg p - 1) = deg q - 1 by ring.
    rewrite BCA.big_seq_cond BCA.big1 ?addr0 //=.
    - move=> i; rewrite mem_range => @/predC1 /= -[[ge0_i lti] ne_i].
      case: (i <= deg p - 1) => [lei|leNi].
      - have: deg q <= deg p + deg q - 2 - i by smt().
        by move/gedeg_coeff => ->; rewrite mulr0.
      - have: deg p <= i by smt().
        by move/gedeg_coeff => ->; rewrite mul0r.
    by apply: mulf_neq0; apply: coeff_degB1_neq0.
- move=> i gei; rewrite polyME BCA.big_seq BCA.big1 //= => j.
  rewrite mem_range => -[ge0_j ltj]; case: (deg p <= j).
  - by move/gedeg_coeff => ->; rewrite mul0r.
  move=> geNj; have leq: deg q <= (i - j) by smt().
  by rewrite mulrC gedeg_coeff -1:mul0r.
qed.

(* -------------------------------------------------------------------- *)
clone import Ring.ZModule as ZPoly with
  type t     <- poly ,
    op zeror <- poly0,
    op (+)   <- polyD,
    op [-]   <- polyN
  proof *.

realize addrA.
proof. by move=> p q r; apply/poly_eqP=> c; rewrite !coeffpE addrA. qed.

realize addrC.
proof. by move=> p q; apply/poly_eqP=> c; rewrite !coeffpE addrC. qed.

realize add0r.
proof. by move=> p; apply/poly_eqP => c; rewrite !coeffpE add0r. qed.

realize addNr.
proof. by move=> p; apply/poly_eqP => c; rewrite !coeffpE addNr. qed.

lemma polyMEw M p q k : (k <= M)%Int => (p * q).[k] =
  BCA.bigi predT (fun i => p.[i] * q.[k-i]) 0 (M+1).
proof.
move=> le_kM; case: (k < 0) => [lt0_k|/lerNgt ge0_k].
+ rewrite lt0_coeff // BCA.big_seq BCA.big1 //= => i.
  case/mem_range=> [ge0_i lt_iM]; rewrite mulf_eq0 (lt0_coeff q) //#.
rewrite (@BCA.big_cat_int (k+1)) 1,2:/# -polyME.
rewrite BCA.big_seq BCA.big1 2:addr0 //= => i /mem_range.
by case=> [lt_ki lt_iM]; rewrite mulf_eq0 (lt0_coeff q) //#.
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
+ by apply: BCA.eq_bigr => /= i _ @/F; rewrite mulrC /#.
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
  by rewrite BCA.mulr_sumr &(BCA.eq_bigr) => /= j _; rewrite mulrA.
rewrite BCA.exchange_big &(BCA.eq_bigr) => /= i _.
by rewrite &(BCA.eq_bigr) => /= j _ /#.
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
by rewrite BCA.big1 //= => i _; rewrite poly0E mul0r.
qed.

lemma mulpDl: left_distributive polyM polyD.
proof.
move=> p q r; apply: poly_eqP => c ge0_c; rewrite !(polyME, polyDE).
by rewrite -BCA.big_split &(BCA.eq_bigr) => /= i _; rewrite polyDE mulrDl.
qed.

lemma onep_neq0 : poly1 <> poly0.
proof. by apply/negP => /poly_eqP /(_ 0); rewrite !polyCE /= oner_neq0. qed.

pred unitp (p : poly) = deg p = 1 /\ Coeff.unit p.[0].

op polyV (p : poly) =
  if deg p = 1 then polyC (Coeff.invr p.[0]) else p.

lemma degV (p : poly) : deg (polyV p) = deg p.
proof.
rewrite /polyV; case: (deg p = 1); last done.
by case/deg_eq1=> c [nz_c ->>]; rewrite !degC polyCE /= invr_eq0.
qed.

clone import Ring.ComRing as PolyRing with
  type t     <- poly ,
    op zeror <- poly0,
    op oner  <- poly1,
    op ( + ) <- polyD,
    op [ - ] <- polyN,
    op ( * ) <- polyM,
    op invr  <- polyV,
    pred unit <- unitp
  proof *.

realize addrA     by apply ZPoly.addrA.
realize addrC     by apply ZPoly.addrC.
realize add0r     by apply ZPoly.add0r.
realize addNr     by apply ZPoly.addNr.
realize mulrA     by apply mulpA.
realize mulrC     by apply mulpC.
realize mul1r     by apply mul1p.
realize mulrDl    by apply mulpDl.
realize oner_neq0 by apply onep_neq0.

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
rewrite polyME BCA.big_int1 /= => /unitP @/unitp -> /=.
by rewrite deg_eq1; exists cp.
qed.

(* -------------------------------------------------------------------- *)
theory BigPoly.
clone include BigComRing with
  type t <- poly,
  pred CR.unit   <- unitp,
    op CR.zeror  <- poly0,
    op CR.oner   <- poly1,
    op CR.( + )  <- polyD,
    op CR.([-])  <- polyN,
    op CR.( * )  <- polyM,
    op CR.invr   <- polyV,
    op CR.intmul <- PolyRing.intmul,
    op CR.ofint  <- PolyRing.ofint,
    op CR.exp    <- PolyRing.exp

    proof CR.*

    rename [theory] "BAdd" as "PCA"
           [theory] "BMul" as "PCM"

    remove abbrev CR.(-)
    remove abbrev CR.(/).

realize CR.addrA     by apply: PolyRing.addrA    .
realize CR.addrC     by apply: PolyRing.addrC    .
realize CR.add0r     by apply: PolyRing.add0r    .
realize CR.addNr     by apply: PolyRing.addNr    .
realize CR.oner_neq0 by apply: PolyRing.oner_neq0.
realize CR.mulrA     by apply: PolyRing.mulrA    .
realize CR.mulrC     by apply: PolyRing.mulrC    .
realize CR.mul1r     by apply: PolyRing.mul1r    .
realize CR.mulrDl    by apply: PolyRing.mulrDl   .
realize CR.mulVr     by apply: PolyRing.mulVr    .
realize CR.unitP     by apply: PolyRing.unitP    .
realize CR.unitout   by apply: PolyRing.unitout  .

lemma polysumE ['a] P F s k :
  (PCA.big<:'a> P F s).[k] = BCA.big P (fun i => (F i).[k]) s.
proof.
elim: s => /= [|x s ih]; first by rewrite poly0E.
rewrite !BCA.big_cons -ih PCA.big_cons /=.
by rewrite -polyDE -(fun_if (fun q => q.[k])).
qed.
end BigPoly.

import BigPoly.

(* -------------------------------------------------------------------- *)
op peval (p : poly) (a : coeff) =
  BCA.bigi predT (fun i => p.[i] * exp a i) 0 (deg p + 1).

(* -------------------------------------------------------------------- *)
abbrev root p a = peval p a = zeror.

end Poly.
