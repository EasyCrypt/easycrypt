(* ==================================================================== *)
require import AllCore Finite List Bigalg Distr.
require import Ring StdOrder IntDiv ZModP Ideal Poly.
(*---*) import IntOrder.

(* ==================================================================== *)
(* This file constructs the ring k[x]/<X^n + 1>                         *)

(* ==================================================================== *)
abstract theory PolyReduce.

clone import PolyComRing as BasePoly
  remove abbrev ( + )
  remove abbrev [ - ]
  remove abbrev ( * ).

(*-*) import Coeff PolyComRing BigPoly BigCf.

(* -------------------------------------------------------------------- *)
clone import IdealComRing as PIdeal with
  type t               <- poly,
    op IComRing.zeror  <- BasePoly.poly0,
    op IComRing.oner   <- BasePoly.poly1,
    op IComRing.( + )  <- BasePoly.PolyComRing.( + ),
    op IComRing.([-])  <- BasePoly.PolyComRing.([-]),
    op IComRing.( * )  <- BasePoly.PolyComRing.( * ),
    op IComRing.invr   <- PolyComRing.invr,
  pred IComRing.unit   <- PolyComRing.unit,
    op BigDom.BAdd.big <- BasePoly.BigPoly.PCA.big<:'a>,
    op BigDom.BMul.big <- BasePoly.BigPoly.PCM.big<:'a>

  proof IComRing.addrA     by exact: PolyComRing.addrA    ,
        IComRing.addrC     by exact: PolyComRing.addrC    ,
        IComRing.add0r     by exact: PolyComRing.add0r    ,
        IComRing.addNr     by exact: PolyComRing.addNr    ,
        IComRing.oner_neq0 by exact: PolyComRing.oner_neq0,
        IComRing.mulrA     by exact: PolyComRing.mulrA    ,
        IComRing.mulrC     by exact: PolyComRing.mulrC    ,
        IComRing.mul1r     by exact: PolyComRing.mul1r    ,
        IComRing.mulrDl    by exact: PolyComRing.mulrDl   ,
        IComRing.mulVr     by exact: PolyComRing.mulVr    ,
        IComRing.unitP     by exact: PolyComRing.unitP    ,
        IComRing.unitout   by exact: PolyComRing.unitout

  remove abbrev IComRing.(-)
  remove abbrev IComRing.(/)

  remove abbrev BigDom.BAdd.bigi
  remove abbrev BigDom.BMul.bigi.

import PCA.

(* -------------------------------------------------------------------- *)
op n : { int | 0 < n } as gt0_n.

lemma ge0_n: 0 <= n by apply/ltrW/gt0_n.

hint exact : gt0_n ge0_n.

(* -------------------------------------------------------------------- *)
lemma deg_XnD1 : deg (exp X n + poly1) = n + 1.
proof. by rewrite deg_polyXnDC. qed.

lemma nz_XnD1 : exp X n + poly1 <> poly0.
proof. by rewrite -deg_eq0 deg_XnD1 addz1_neq0. qed.

hint exact : nz_XnD1.

(* -------------------------------------------------------------------- *)
op I = idgen [exp X n + poly1].

lemma idI : ideal I by apply: ideal_idgen.

hint exact : idI.

(* -------------------------------------------------------------------- *)
type polyXnD1.

clone include RingQuotient
  with type qT <- polyXnD1, op p <- I

  proof IdealAxioms.*

  rename [op] "zeror" as "zeroXnD1"
  rename [op] "oner"  as "oneXnD1".

realize IdealAxioms.ideal_p by apply/idI.

realize IdealAxioms.ideal_Ntriv.
proof.
move=> p un_p; rewrite ideal_eq1P 1:&(idI) //; apply/negP.
move/fun_ext => /(_ poly1); rewrite mem_idT /I mem_idgen1.
case/eqT=> q /(congr1 deg); rewrite deg1 => /eq_sym.
case: (q = poly0) => [->|nz_q]; first by rewrite mul0r deg0.
rewrite degM_proper; 1: by rewrite lc_polyXnDC // mulr1 lc_eq0.
rewrite deg_polyXnDC // -!addrA /= gtr_eqF //.
by rewrite (_ : 1 = 1 + 0) 1:// ler_lt_add // deg_ge1.
qed.

(* -------------------------------------------------------------------- *)
clone BigComRing as BigXnD1 with
  type CR.t      <- polyXnD1,
    op CR.zeror  <- zeroXnD1,
    op CR.oner   <- oneXnD1,
    op CR.( + )  <- ( + ),
    op CR.([-])  <- ([-]),
    op CR.( * )  <- ( * ),
    op CR.invr   <- invr,
    op CR.intmul <- ComRing.intmul,
    op CR.ofint  <- ComRing.ofint,
    op CR.exp    <- ComRing.exp,
    op CR.lreg   <- ComRing.lreg,
  pred CR.unit   <- unit

  proof *

  remove abbrev CR.(-)
  remove abbrev CR.(/)

  rename [theory] "BAdd" as "XnD1CA"
         [theory] "BMul" as "XnD1CM".

realize CR.addrA     by apply: ComRing.addrA    .
realize CR.addrC     by apply: ComRing.addrC    .
realize CR.add0r     by apply: ComRing.add0r    .
realize CR.addNr     by apply: ComRing.addNr    .
realize CR.oner_neq0 by apply: ComRing.oner_neq0.
realize CR.mulrA     by apply: ComRing.mulrA    .
realize CR.mulrC     by apply: ComRing.mulrC    .
realize CR.mul1r     by apply: ComRing.mul1r    .
realize CR.mulrDl    by apply: ComRing.mulrDl   .
realize CR.mulVr     by apply: ComRing.mulVr    .
realize CR.unitP     by apply: ComRing.unitP    .
realize CR.unitout   by apply: ComRing.unitout  .

import BigXnD1.

(* -------------------------------------------------------------------- *)
abbrev pinject = pi.
abbrev prepr   = repr.

(* -------------------------------------------------------------------- *)
op iX = pinject X.

(* -------------------------------------------------------------------- *)
op ( ** ) (c : coeff) (p : polyXnD1) =
  pinject (c ** (repr p)).

(* -------------------------------------------------------------------- *)
lemma scale0p (p : polyXnD1) : Coeff.zeror ** p = zeroXnD1.
proof. by rewrite /( ** ) scale0p. qed.

(* -------------------------------------------------------------------- *)
lemma scaleE c (p : poly) : c ** pi p = pinject (c ** p).
proof. by rewrite /( ** ) !scalepE -2!mulE reprK. qed.

(* -------------------------------------------------------------------- *)
lemma eqv_Xn : eqv (exp X n) (-poly1).
proof. by rewrite eqv_sym /eqv opprK /I mem_idgen1_gen. qed.

(* -------------------------------------------------------------------- *)
op reduce (p : poly) : poly =
  PCA.bigi predT
    (fun i => (exp (-Coeff.oner) (i %/ n) * p.[i]) ** exp X (i %% n))
    0 (deg p).

op reduced (p : poly) = (reduce p = p).

(* -------------------------------------------------------------------- *)
lemma reducewE k (p : poly) : deg p <= k =>
  reduce p = PCA.bigi predT
    (fun i => (exp (-Coeff.oner) (i %/ n) * p.[i]) ** exp X (i %% n))
    0 k.
proof.
move=> len; rewrite (PCA.big_cat_int (deg p)) ?ge0_deg // /reduce.
pose c := big _ _ _; rewrite PCA.big_seq PCA.big1 /= ?addr0 //.
by move=> i /mem_range [gei _]; rewrite gedeg_coeff // mulr0 scale0p.
qed.

(* -------------------------------------------------------------------- *)
lemma deg_reduce p : deg (reduce p) <= n.
proof.
apply: deg_sum => //= i _; apply: (ler_trans _ _ _ (degZ_le _ _)).
by rewrite deg_polyXn ?(modz_ge0, gtr_eqF) // -ltzE ltz_pmod.
qed.

(* -------------------------------------------------------------------- *)
lemma deg_reduced p : reduced p => deg p <= n.
proof. by move=> @/reduced => <-; rewrite deg_reduce. qed.

(* -------------------------------------------------------------------- *)
lemma eqv_reduce (p : poly) : eqv p (reduce p).
proof.
rewrite {1}(polyE p) /reduce !PCA.big_seq &(eqv_sum) /=.
move=> i /mem_range [rg_i _]; rewrite mulrC -scalepA.
pose q := exp X (i %/ n * n) * exp X (i %% n).
rewrite !scalepE &(eqvMl) &(eqv_trans q).
- rewrite (_ : q = exp X i) // /q -exprD_nneg // -?divz_eq //.
  - by rewrite mulr_ge0 // divz_ge0.
  - by rewrite modz_ge0 gtr_eqF.
apply/eqvMr; rewrite -polyCX ?divz_ge0 // (IntID.mulrC _ n).
by rewrite exprM eqvX polyCN eqv_Xn.
qed.

(* -------------------------------------------------------------------- *)
lemma eqv_reducel (p q : poly) : eqv p (reduce q) <=> eqv p q.
proof. split.
- by move/eqv_trans; apply; rewrite eqv_sym &(eqv_reduce).
- by move/(eqv_trans _ _ (reduce q))/(_ (eqv_reduce q)).
qed.

(* -------------------------------------------------------------------- *)
lemma eqv_reducer (p q : poly) : eqv (reduce p) q <=> eqv p q.
proof. by rewrite eqv_sym eqv_reducel eqv_sym. qed.

(* -------------------------------------------------------------------- *)
lemma reduce_eqP (p q : poly) : (reduce p = reduce q) <=> (eqv p q).
proof.
split=> [eq_rd|eqv_pq].
- by rewrite -eqv_reducel -eqv_reducer eq_rd eqvxx.
have @/eqv @/I: eqv (reduce p) (reduce q).
- by rewrite !(eqv_reducel, eqv_reducer).
case/mem_idgen1=> r /(congr1 deg); case: (r = poly0) => [->>|nz_r].
- by rewrite mul0r deg0 deg_eq0 subr_eq0 => ->.
have: deg (reduce q - reduce p) <= n.
- by rewrite &(ler_trans _ _ _ (degB _ _)) ler_maxrP !deg_reduce.
rewrite degM_proper.
- by rewrite mulrC mulrI_eq0 ?lc_eq0 // lc_polyXnDC // &(Coeff.lreg1).
move=> + eqd; rewrite eqd deg_XnD1 -!addrA /=.
rewrite addrC -ler_subr_addl /= ler_eqVlt deg_eq0.
by rewrite nz_r /= ltrNge ge0_deg.
qed.

(* -------------------------------------------------------------------- *)
lemma reducedP p : (reduced p) <=> (deg p <= n).
proof.
split; first by move=> @/reduced <-; apply/deg_reduce.
move=> led; rewrite /reduced {2}polyE /reduce.
rewrite !big_seq &(eq_bigr) => /= i /mem_range rg_i.
by rewrite pmod_small 1:/# pdiv_small 1:/# expr0 mul1r.
qed.

(* -------------------------------------------------------------------- *)
lemma reduced_reduce p : reduced (reduce p).
proof. by rewrite reducedP &(deg_reduce). qed.

(* -------------------------------------------------------------------- *)
lemma reduceK p : reduce (reduce p) = reduce p.
proof. by apply: reduced_reduce. qed.

(* -------------------------------------------------------------------- *)
lemma reduce_reduced p : reduced p => reduce p = p.
proof. by []. qed.

(* -------------------------------------------------------------------- *)
op crepr (p : polyXnD1) = reduce (repr p).

abbrev "_.[_]" p i = (crepr p).[i].

lemma reduced_crepr p : reduced (crepr p).
proof. by apply: reduced_reduce. qed.

lemma piK p : reduced p => crepr (pi p) = p.
proof.
move=> red_p @/crepr; rewrite -{2}red_p.
by apply/reduce_eqP/eqv_repr.
qed.

lemma creprK p : pi (crepr p) = p.
proof.
rewrite /crepr; have ->: pi (reduce (repr p)) = pi (repr p).
- by rewrite -eqv_pi eqv_sym eqv_reduce.
- by apply reprK.
qed.

lemma deg_crepr p : deg (crepr p) <= n.
proof.
by apply deg_reduce.
qed.
 
(* -------------------------------------------------------------------- *)
lemma polyXnD1W P :
  (forall p, reduced p => P (pi p)) => forall p, P p.
proof.
move=> ih p; rewrite (_ : p = pi (crepr p)).
- by rewrite -{1}(reprK p) &(eqv_pi) eqv_reduce.
- by apply/ih/reduced_reduce.
qed.

(* -------------------------------------------------------------------- *)
lemma polyXnD1_eqP (p q : polyXnD1) :
  (p = q) <=> (forall i, 0 <= i < n => p.[i] = q.[i]).
proof.
elim/polyXnD1W: p => p redp; elim/polyXnD1W: q => q redq.
rewrite !piK // -eqv_pi -reduce_eqP !reduce_reduced //.
split=> [->//|eq_pq]; apply/poly_eqP => i ge0_i.
case: (i < n) => [lt_in|/lerNgt le_ni]; first by apply/eq_pq.
by rewrite !gedeg_coeff //; smt(reducedP).
qed.

(* -------------------------------------------------------------------- *)
lemma reduced_polyL xs : size xs <= n => reduced (polyL xs).
proof. by move=> len; apply/reducedP/(ler_trans (size xs))/len/degL_le. qed.

(* -------------------------------------------------------------------- *)
lemma reducedC c : reduced (polyC c).
proof. by rewrite reducedP degC; smt(gt0_n). qed.

(* -------------------------------------------------------------------- *)
lemma reduced0 : reduced poly0.
proof. by apply: reducedC. qed.

(* -------------------------------------------------------------------- *)
lemma reduced1 : reduced poly1.
proof. by apply: reducedC. qed.

(* -------------------------------------------------------------------- *)
lemma lt0_rcoeff p i : i < 0 => p.[i] = Coeff.zeror.
proof. by move=> gt0_i; rewrite lt0_coeff. qed.

(* -------------------------------------------------------------------- *)
lemma gered_rcoeff p i : n <= i => p.[i] = Coeff.zeror.
proof.
move=> ge_ni; rewrite gedeg_coeff //.
by apply/(ler_trans n)/ge_ni/deg_crepr.
qed.

(* -------------------------------------------------------------------- *)
lemma rcoeff0 k : zeroXnD1.[k] = Coeff.zeror.
proof. by rewrite piK 1:reduced0 poly0E. qed.

(* -------------------------------------------------------------------- *)
lemma reducedD (p q : poly) : reduced p => reduced q => reduced (p + q).
proof.
rewrite !reducedP => dgp dgq;
  apply: (ler_trans _ _ _ (degD _ _ ));
  by rewrite ler_maxrP.
qed.

(* -------------------------------------------------------------------- *)
lemma rcoeffD (p q : polyXnD1) k : (p + q).[k] = p.[k] + q.[k].
proof.
elim/polyXnD1W: p => p rdp; elim/polyXnD1W: q => q rdq.
by rewrite addE !piK 1:&(reducedD) // polyDE.
qed.

(* -------------------------------------------------------------------- *)
lemma reduced_sum ['a] (P : 'a -> bool) (F : 'a -> poly) (r : 'a list) :
  (forall i, P i => reduced (F i)) => reduced (PCA.big P F r).
proof.
move=> red; elim: r => [|x r ih]; 1: by rewrite big_nil reduced0.
by rewrite big_cons; case: (P x) => // Px; rewrite reducedD // &(red).
qed.

(* -------------------------------------------------------------------- *)
lemma rcoeff_sum ['a] (P : 'a -> bool) (F : 'a -> polyXnD1) (r : 'a list) k :
  (XnD1CA.big P F r).[k] = BCA.big P (fun i => (F i).[k]) r.
proof.
elim: r => [|x r ih].
- by rewrite XnD1CA.big_nil BCA.big_nil rcoeff0.
rewrite XnD1CA.big_cons BCA.big_cons.
by case: (P x) => Px; rewrite ?rcoeffD ih.
qed.

(* -------------------------------------------------------------------- *)
lemma reducedZ c p : reduced p => reduced (c ** p).
proof. by rewrite !reducedP => degp; apply/(ler_trans (deg p))/degp/degZ_le. qed.

(* -------------------------------------------------------------------- *)
lemma rcoeffZ c p k : (c ** p).[k] = c * p.[k].
proof.
case: (c = Coeff.zeror) => [->|nz_c]; 1: by rewrite scale0p rcoeff0 mul0r.
elim/polyXnD1W: p => p redp; rewrite scaleE.
by rewrite !piK 1:&(reducedZ) // polyZE.
qed.

(* -------------------------------------------------------------------- *)
lemma reducedXn i : 0 <= i < n => reduced (exp X i).
proof.
by case=> ge0_i lt_in; rewrite reducedP (ler_trans (i+1)) 1:deg_polyXn //#.
qed.

(* -------------------------------------------------------------------- *)
lemma rcoeff_polyXn i k : 0 <= i < n =>
  (ComRing.exp iX i).[k] = if k = i then Coeff.oner else Coeff.zeror.
proof. admitted.

(* -------------------------------------------------------------------- *)
lemma rcoeffM (p q : polyXnD1) k : 0 <= k < n => (p * q).[k] =
    BCA.bigi predT (fun i =>
       p.[i] * q.[k - i] - p.[i] * q.[n + k - i]) 0 n.
proof.
case=> ge0_k le_kn; elim/polyXnD1W: p => p rdp; elim/polyXnD1W: q => q rdq.
rewrite mulE {1}/crepr; pose r := reduce _; have ->: r = reduce (p * q).
- by apply/reduce_eqP/eqv_repr.
rewrite (polywE n (reduce (p * q))) 1:&(deg_reduce).
rewrite (PCA.bigD1 _ _ k) ?(mem_range, range_uniq) /= 1:/#.
rewrite polyDE; pose c := (bigi _ _ _ _); have ->: c.[k] = Coeff.zeror.
- rewrite /c polysumE BCA.big_seq_cond BCA.big1 ?addr0 //=.
  move=> i [/mem_range [ge0_i lt_in] @/predC1 ne_ik].
  by rewrite polyZE polyXnE // (eq_sym k i) ne_ik /= mulr0.
rewrite addr0 polyZE polyXnE //= mulr1 (reducewE (2 * n)).
- case: (p = poly0) => [->|nz_p]; first by rewrite mul0r deg0 /#.
  case: (q = poly0) => [->|nz_q]; first by rewrite mulr0 deg0 /#.
  apply: (ler_trans (deg p + deg q)); last first.
  - by rewrite (_ : 2 * n = n + n) 1:#ring ler_add &(deg_reduced).
  by rewrite &(ler_trans (deg (p * q) + 1)) ?ler_addl // &(degM_le).
rewrite (PCA.bigD1 _ _ k) /= ?(mem_range, range_uniq) 1:/#.
rewrite (PCA.bigD1_cond _ _ _ (n+k)) /= ?(mem_range, range_uniq) 1,2://#.
rewrite PCA.big_seq_cond !polyDE polysumE BCA.big1 /= => [i|].
- case=> [/mem_range [ge0_i lei] [@/predC1 ne_ik ne_i_nDk]].
  rewrite polyZE polyXnE; first by rewrite modz_ge0 gtr_eqF.
  case: (k = i %% n) => [kE|]; last by rewrite mulr0.
  suff //: false; move: ne_ik ne_i_nDk.
  have rg_in: 0 <= i %/ n < 2 by rewrite divz_ge0 // ltz_divLR.
  by rewrite (divz_eq i n) kE /#.
rewrite !polyZE !polyXnE; 1,2: by rewrite modz_ge0 gtr_eqF.
rewrite modzDl pmod_small // /= !mulr1 addr0.
rewrite pdiv_small // expr0 mul1r divzDl ?dvdzz divzz.
rewrite (gtr_eqF n) // pdiv_small //= expr1 mulN1r.
rewrite -BCA.sumrB; do 2? congr.
- by rewrite (polyMEw (n-1)) 1:/# /= &(BCA.eq_bigr) /= => i; rewrite !piK.
rewrite polyME (BCA.big_cat_int n) 1,2://#.
rewrite addrC BCA.big_seq BCA.big1 ?addr0 /=.
- move=> i /mem_range [??]; rewrite gedeg_coeff ?mul0r //.
  by apply: (ler_trans n) => //; apply/deg_reduced.
by rewrite add0r &(BCA.eq_bigr) => i; rewrite !piK.
qed.

(* -------------------------------------------------------------------- *)
lemma finite_for_polyXnD1 s :
     is_finite_for predT s
  => is_finite_for predT (map (pi \o polyL) (alltuples n s)).
proof.
move=> fin_coeff; pose P p := (deg p <= n); rewrite map_comp.
apply: (is_finite_for_bij _ P) => [|p q|q].
- have := finite_for_poly_ledeg n predT s fin_coeff.
  - by apply/eq_is_finite_for => q; rewrite /max /P /predT gt0_n.
- by move=> @/P dgp dgq /(congr1 crepr); rewrite !piK ?reducedP.
- exists (crepr q); rewrite /P deg_reduced ?reduced_crepr //=.
  by have /eqv_pi := eqv_reduce (repr q) => @/crepr <-; rewrite reprK.
qed.
end PolyReduce.

(* ==================================================================== *)
abstract theory PolyReduceZp.
type Zp.

op p : { int | 2 <= p } as ge2_p.

clone import ZModRing as Zp with
    type  zmod  <- Zp,
    op    p     <- p
    proof ge2_p by exact/ge2_p.

clone include PolyReduce with
    type BasePoly.coeff        <- Zp,
    pred BasePoly.Coeff.unit   <- Zp.unit,
    op   BasePoly.Coeff.zeror  <- Zp.zero,
    op   BasePoly.Coeff.oner   <- Zp.one,
    op   BasePoly.Coeff.( + )  <- Zp.( + ),
    op   BasePoly.Coeff.([-])  <- Zp.([-]),
    op   BasePoly.Coeff.( * )  <- Zp.( * ),
    op   BasePoly.Coeff.invr   <- Zp.inv,
    op   BasePoly.Coeff.ofint  <- Zp.ZModpRing.ofint,
    op   BasePoly.Coeff.exp    <- Zp.ZModpRing.exp,
    op   BasePoly.Coeff.intmul <- Zp.ZModpRing.intmul,
    op   BasePoly.Coeff.lreg   <- Zp.ZModpRing.lreg

  proof BasePoly.Coeff.addrA     by exact Zp.ZModpRing.addrA
  proof BasePoly.Coeff.addrC     by exact Zp.ZModpRing.addrC
  proof BasePoly.Coeff.add0r     by exact Zp.ZModpRing.add0r
  proof BasePoly.Coeff.addNr     by exact Zp.ZModpRing.addNr
  proof BasePoly.Coeff.oner_neq0 by exact Zp.ZModpRing.oner_neq0
  proof BasePoly.Coeff.mulrA     by exact Zp.ZModpRing.mulrA
  proof BasePoly.Coeff.mulrC     by exact Zp.ZModpRing.mulrC
  proof BasePoly.Coeff.mul1r     by exact Zp.ZModpRing.mul1r
  proof BasePoly.Coeff.mulrDl    by exact Zp.ZModpRing.mulrDl
  proof BasePoly.Coeff.mulVr     by exact Zp.ZModpRing.mulVr
  proof BasePoly.Coeff.unitP     by exact Zp.ZModpRing.unitP
  proof BasePoly.Coeff.unitout   by exact Zp.ZModpRing.unitout
  proof BasePoly.Coeff.*

  remove abbrev BasePoly.Coeff.(-)
  remove abbrev BasePoly.Coeff.(/).

clear [BasePoly.Coeff.*].
clear [BasePoly.Coeff.AddMonoid.*].
clear [BasePoly.Coeff.MulMonoid.*].

(* -------------------------------------------------------------------- *)
import BasePoly.

(* ==================================================================== *)
(* We already know that polyXnD1 is finite. However, we prove here that *)
(* we can build the full-uniform distribution over polyXnD1 by sampling *)
(* uniformly each coefficient in the reduced form representation.       *)

op dpolyXnD1 = dmap (dpoly n Zp.DZmodP.dunifin) pinject.

lemma dpolyXnD1_uni : is_uniform dpolyXnD1.
proof.
apply/dmap_uni_in_inj/dpoly_uni/DZmodP.dunifin_uni => //.
move=> p q; rewrite !supp_dpoly //; case=> [degp _] [deqq _].
by move/eqv_pi/reduce_eqP; rewrite !reduce_reduced // !reducedP.
qed.

lemma dpolyXnD1_fu : is_full dpolyXnD1.
proof.
apply/dmap_fu_in=> p; exists (crepr p); rewrite creprK /=.
by apply/dpoly_fu/deg_crepr => //; rewrite DZmodP.dunifin_fu.
qed.

lemma dpolyXnD1_ll : is_lossless dpolyXnD1.
proof. by apply/dmap_ll/dpoly_ll/DZmodP.dunifin_ll. qed.

lemma dpolyXnD1_funi : is_funiform dpolyXnD1.
proof. by apply/is_full_funiform/dpolyXnD1_uni/dpolyXnD1_fu. qed.
end PolyReduceZp.
