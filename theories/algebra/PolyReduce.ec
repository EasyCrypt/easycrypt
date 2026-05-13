(* ==================================================================== *)
require import AllCore Finite List Bigalg Distr.
require import Ring StdOrder IntDiv ZModP Ideal Poly.
(*---*) import IntOrder.

(* ==================================================================== *)
(* This file constructs the ring k[x]/<X^n + 1>                         *)

(* ==================================================================== *)
abstract theory PolyReduce.
type coeff.

clone import ComRing as Coeff with type t <= coeff.

clone export PolyComRing as BasePoly
  with type   coeff <- coeff,
       theory Coeff <- Coeff.

import Coeff BigPoly BigCf.

(* -------------------------------------------------------------------- *)
clone import IdealComRing as PIdeal with
    type t               <- BasePoly.poly,
  theory IComRing        <- BasePoly.PolyComRing,
      op BigDom.BAdd.big <- BasePoly.BigPoly.PCA.big<:'a>,
      op BigDom.BMul.big <- BasePoly.BigPoly.PCM.big<:'a>

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

clone include RingQuotientDflInv with
  op p <- I
  proof IdealAxioms.*
  rename "qT" as "polyXnD1".

realize IdealAxioms.ideal_p by apply/idI.

realize IdealAxioms.ideal_Ntriv.
proof.
move=> p un_p; rewrite ideal_eq1P 1:&(idI) //; apply/negP.
move/fun_ext => /(_ poly1); rewrite mem_idT /I mem_idgen1.
case/eqT=> q /(congr1 deg); rewrite deg1 => /eq_sym.
case: (q = poly0) => [->|nz_q]; first by rewrite /( * ) mul0r deg0.
rewrite degM_proper; 1: by rewrite lc_polyXnDC // mulr1 lc_eq0.
rewrite deg_polyXnDC // -!addrA /= gtr_eqF //.
by rewrite (_ : 1 = 1 + 0) 1:// ler_lt_add // deg_ge1.
qed.

op zeroXnD1 = zeror.
op oneXnD1 = oner.

(* -------------------------------------------------------------------- *)
clone BigComRing as BigXnD1 with
  theory CR <= ComRingDflInv
  proof *

  remove abbrev CR.(-)
  remove abbrev CR.(/)

  rename [theory] "BAdd" as "XnD1CA"
         [theory] "BMul" as "XnD1CM".

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
op pevalX (p : polyXnD1) (c : coeff) =
  peval (repr p) c.

op polyLX (a : coeff list) : polyXnD1 = pinject (polyL a).

op polyCX (c : coeff) = pinject (polyC c).

(* -------------------------------------------------------------------- *)
lemma scale0p (p : polyXnD1) : Coeff.zeror ** p = zeroXnD1.
proof. by rewrite /( ** ) scale0p. qed.

(* -------------------------------------------------------------------- *)
lemma scaleDl (c1 c2 : coeff) (p : polyXnD1) : 
  (c1 + c2) ** p = (c1 ** p) + (c2 ** p).
proof. by rewrite /( ** ) scalepDl addE. qed.

lemma scaleN (c : coeff) p : (-c) ** p = - (c ** p).
proof. by rewrite /( ** ) scaleNp oppE. qed.

(* -------------------------------------------------------------------- *)
lemma scaleE c (p : poly) : c ** pi p = pinject (c ** p).
proof. by rewrite /( ** ) !scalepE -2!mulE reprK. qed.

(* -------------------------------------------------------------------- *)
lemma eqv_Xn : eqv (exp X n) (-poly1).
proof.  rewrite eqv_sym /eqv /[-] opprK /I mem_idgen1_gen. qed.

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
- rewrite (_ : q = exp X i) // /q /( * ) -exprD_nneg // -?divz_eq //.
  - by rewrite mulr_ge0 // divz_ge0.
  - by rewrite modz_ge0 gtr_eqF.
apply/eqvMr; rewrite -polyCX ?divz_ge0 // (IntID.mulrC _ n).
rewrite exprM eqvX; first smt(gt0_n).
by rewrite polyCN eqv_Xn.
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
- by rewrite /( * ) mul0r deg0 deg_eq0 subr_eq0 => ->.
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
move=> led; rewrite /reduced {2}[p]polyE /reduce.
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
lemma reducedN (p : poly) : reduced p => reduced (- p).
proof. by rewrite !reducedP degN. qed.

(* -------------------------------------------------------------------- *)
lemma rcoeffN (p : polyXnD1) k : - p.[k] = (- p).[k].
proof.
by elim/polyXnD1W: p => p rdp; rewrite oppE !piK 2:reducedN 3: polyNE.
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
lemma polyXnD1_sumN ['a] (P : 'a -> bool) (F : 'a -> polyXnD1) (r : 'a list) :
  - (XnD1CA.big P F r) = (XnD1CA.big P (fun i => - (F i)) r).
proof.
rewrite XnD1CA.big_endo //.
+ by rewrite ComRingDflInv.oppr0.
+ by apply ComRingDflInv.opprD. 
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
lemma eq_expiXn_expXn i : 0 <= i < n => ComRingDflInv.exp iX i = pi (exp X i).
move => [ge0i ltni]; elim: i ge0i ltni => [| i ge0_i ih ltn_i1].
+ by rewrite ComRingDflInv.expr0 expr0.
+ by rewrite ComRingDflInv.exprS 2:exprS // -mulE ih /#.
qed.

lemma rcoeff_polyXn i k : 0 <= i < n =>
  (ComRingDflInv.exp iX i).[k] = if k = i then Coeff.oner else Coeff.zeror.
proof. 
move => rng_i; rewrite eq_expiXn_expXn 1:rng_i piK 1:reducedXn 2:polyXnE //#.
qed.

(* -------------------------------------------------------------------- *)
lemma rcoeffZ_sum (F : int -> coeff) (k : int) : 
  0 <= k < n =>
  (XnD1CA.bigi predT (fun i => (F i) ** ComRingDflInv.exp iX i) 0 n).[k] = F k.
proof.
move => rng_k; rewrite rcoeff_sum (BCA.bigD1 _ _ k) /=.
+ by rewrite mem_range.
+ by rewrite range_uniq.
rewrite BCA.big_seq_cond BCA.big1 => [i [/mem_range rng_i @/predC1 ne_ik]|]. 
+ by rewrite /= rcoeffZ rcoeff_polyXn // (eq_sym k) ne_ik /= mulr0.
+ by rewrite addr0 rcoeffZ rcoeff_polyXn //= mulr1.
qed.

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
- case: (p = poly0) => [->|nz_p]; first by rewrite /( * ) mul0r deg0 /#.
  case: (q = poly0) => [->|nz_q]; first by rewrite /( * ) mulr0 deg0 /#.
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

lemma polyLXE coeffs i :
  size coeffs <= n =>
  (polyLX coeffs).[i] = nth Coeff.zeror coeffs i.
proof. by move=> h; rewrite piK 1:reduced_polyL // &(polyLE). qed.

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

clone import ZModRing as Zp.

clone import PolyReduce with
    type coeff <= Zp.zmod,
  theory Coeff <= ZModpRing.

(* ==================================================================== *)
(* We already know that polyXnD1 is finite. However, we prove here that *)
(* we can build the full-uniform distribution over polyXnD1 by sampling *)
(* uniformly each coefficient in the reduced form representation.       *)

op dpolyX (dcoeff : zmod distr) : polyXnD1 distr =
  dmap (dpoly n dcoeff) pinject.

lemma dpolyX_ll d : is_lossless d => is_lossless (dpolyX d).
proof. by move=> ll_d; apply/dmap_ll/BasePoly.dpoly_ll. qed.

lemma dpolyX_uni d : is_uniform d => is_uniform (dpolyX d).
proof.
move=> uni_d; apply/dmap_uni_in_inj/dpoly_uni/uni_d => //.
move=> p q; rewrite !supp_dpoly //; case=> [degp _] [deqq _].
by move/eqv_pi/reduce_eqP; rewrite !reduce_reduced // !reducedP.
qed.

lemma dpolyX_full d : is_full d => is_full (dpolyX d).
proof.
move=> fu_d; apply/dmap_fu_in=> p; exists (crepr p).
by rewrite creprK /=; apply/dpoly_fu/deg_crepr.
qed.

lemma dpolyX_suppP d p :
  p \in dpolyX d <=> (forall i, 0 <= i < n => p.[i] \in d).
proof. split.
- case/supp_dmap=> q [+ ->>] i rg_i.
  rewrite supp_dpoly => // -[? /(_ i rg_i)].
  by rewrite piK //; apply/reducedP.
- move=> h; apply/supp_dmap; exists (crepr p).
  by rewrite creprK /= &(supp_dpoly) // deg_crepr.
qed.

(* -------------------------------------------------------------------- *)
op dpolyXnD1 = dpolyX Zp.DZmodP.dunifin.

lemma dpolyXnD1_ll : is_lossless dpolyXnD1.
proof. by apply/dpolyX_ll/DZmodP.dunifin_ll. qed.

lemma dpolyXnD1_uni : is_uniform dpolyXnD1.
proof. by apply/dpolyX_uni/DZmodP.dunifin_uni. qed.

lemma dpolyXnD1_full : is_full dpolyXnD1.
proof. by apply/dpolyX_full/DZmodP.dunifin_fu. qed.

lemma dpolyXnD1_funi : is_funiform dpolyXnD1.
proof. by apply/is_full_funiform/dpolyXnD1_uni/dpolyXnD1_full. qed.

(* -------------------------------------------------------------------- *)
lemma reduced_dpoly d p : p \in dpoly n d => reduced p.
proof. by rewrite supp_dpoly // => -[ltn_deg _]; apply/reducedP. qed.

end PolyReduceZp.

(* ==================================================================== *)
(* PolyReduceZpCentered: same scaffolding as [PolyReduceZp] but the     *)
(* coefficient sub-theory is [ZqCentered] (extends [ZModRing] with     *)
(* centered representation [crepr], absolute value `|_|`, and the      *)
(* abs_zp lemma family).                                                *)
(*                                                                      *)
(* Built by first cloning [ZqCentered] (to get the extended Zp), then  *)
(* clone-including [PolyReduceZp] with PolyReduceZp's internal Zp       *)
(* rebound to ours — so the polynomial-ring construction and the       *)
(* distributions are inherited without copy-paste.                     *)
(* ==================================================================== *)
require import ZModPCentered Nneg.
require DynMatrix.

abstract theory PolyReduceZpCentered.

clone include ZpCenteredRing.

clone include PolyReduceZp with
  theory Zp <- ZMR.
import PolyReduce.
import ZMR.

(* ==================================================================== *)
(* Centered-representation infinity-norm machinery on polyXnD1.         *)
(*                                                                      *)
(* Two complementary views, equivalent under non-negative bounds:       *)
(*   - predicate-style checks: poly_infnorm_le, poly_infnorm_lt         *)
(*   - computed norm: inf_norm : polyXnD1 -> Nneg.nneg                   *)
(* The soundness lemmas tie them together.                               *)
(* ==================================================================== *)

(* -------------------------------------------------------------------- *)
(* Predicate-style inf-norm bound checks on coefficients.                *)

op poly_infnorm_lt (q : polyXnD1) (b : int) : bool =
  forall i, 0 <= i < n => `|q.[i]| < b.

op poly_infnorm_le (q : polyXnD1) (b : int) : bool =
  forall i, 0 <= i < n => `|q.[i]| <= b.

(* -------------------------------------------------------------------- *)
(* Basic monotonicity / equivalence lemmas.                              *)

lemma poly_infnorm_lt_le (q : polyXnD1) (b : int) :
  poly_infnorm_lt q b => poly_infnorm_le q b.
proof. by move=> H i Hi; have := H i Hi; smt(). qed.

lemma poly_infnorm_le_mono (q : polyXnD1) (b1 b2 : int) :
  b1 <= b2 => poly_infnorm_le q b1 => poly_infnorm_le q b2.
proof. by move=> Hb H i Hi; have := H i Hi; smt(). qed.

lemma poly_infnorm_lt_mono (q : polyXnD1) (b1 b2 : int) :
  b1 <= b2 => poly_infnorm_lt q b1 => poly_infnorm_lt q b2.
proof. by move=> Hb H i Hi; have := H i Hi; smt(). qed.

(* -------------------------------------------------------------------- *)
(* Trivial bounds.                                                       *)

lemma poly_infnorm_le_ub (q : polyXnD1) :
  poly_infnorm_le q (p %/ 2)
  by move=> i Hi; smt(abs_zp_ub).

lemma poly_infnorm_le_zero :
  poly_infnorm_le zeroXnD1 0.
proof. move=> i Hi; rewrite rcoeff0; smt(abs_zp_zero). qed.

(* -------------------------------------------------------------------- *)
(* Triangle inequality and negation bounds.                              *)

lemma poly_infnorm_le_add (q r : polyXnD1) (bq br : int) :
     poly_infnorm_le q bq
  => poly_infnorm_le r br
  => poly_infnorm_le (q + r) (bq + br).
proof.
move=> Hq Hr i Hi.
rewrite rcoeffD; have := abs_zp_triangle q.[i] r.[i].
have := Hq i Hi; have := Hr i Hi; smt().
qed.

lemma poly_infnorm_lt_add (q r : polyXnD1) (bq br : int) :
     poly_infnorm_lt q bq
  => poly_infnorm_lt r br
  => poly_infnorm_lt (q + r) (bq + br).
proof.
move=> Hq Hr i Hi.
rewrite rcoeffD; have := abs_zp_triangle q.[i] r.[i].
have := Hq i Hi; have := Hr i Hi; smt().
qed.

lemma poly_infnorm_le_opp (q : polyXnD1) (b : int) :
  poly_infnorm_le q b => poly_infnorm_le (- q) b.
proof.
move=> H i Hi.
rewrite -rcoeffN -abs_zpN.
have := H i Hi; smt().
qed.

lemma poly_infnorm_lt_opp (q : polyXnD1) (b : int) :
  poly_infnorm_lt q b => poly_infnorm_lt (- q) b.
proof.
move=> H i Hi.
rewrite -rcoeffN -abs_zpN.
have := H i Hi; smt().
qed.

(* -------------------------------------------------------------------- *)
(* Computed inf-norm via big-max of coefficient absolute values.        *)

op inf_norm (q : polyXnD1) : Nneg.nneg =
  Nneg.BMaxN.bigi predT (fun i => Nneg.ofint `|q.[i]|) 0 n.

(* Soundness against the [_le] check (for non-negative bounds). *)
lemma poly_infnorm_le_iff (q : polyXnD1) (b : int) :
  0 <= b =>
  (poly_infnorm_le q b <=> Nneg.(<=) (inf_norm q) (Nneg.ofint b)).
proof.
move=> ge0_b; rewrite /poly_infnorm_le /inf_norm Nneg.BMaxN.big_le_iff.
have valK_b : Nneg.val (Nneg.ofint b) = b by apply Nneg.valK_pos.
have step : forall a, 0 <= a =>
  Nneg.(<=) (Nneg.ofint a) (Nneg.ofint b) <=> a <= b.
- move=> a ge0_a; rewrite /Nneg.(<=) valK_b.
  by have -> : Nneg.val (Nneg.ofint a) = a by apply Nneg.valK_pos.
split.
- move=> H; split; first by apply Nneg.zero_le.
  move=> i; rewrite mem_range => Hi _ /=.
  have ge0_a : 0 <= `|q.[i]| by smt().
  by rewrite step //; apply H; smt().
- case=> _ H i Hi.
  have Hi' : i \in range 0 n by rewrite mem_range; smt().
  have ge0_a : 0 <= `|q.[i]| by smt().
  have := H i Hi' _; first by [].
  by rewrite /= step.
qed.

(* Soundness against the [_lt] check. Strictly-less bound means         *)
(* coefficient bounds by [b - 1] (since values are integers).           *)
lemma poly_infnorm_lt_iff (q : polyXnD1) (b : int) :
  1 <= b =>
  (poly_infnorm_lt q b <=> Nneg.(<=) (inf_norm q) (Nneg.ofint (b - 1))).
proof.
move=> ge1_b.
have -> : poly_infnorm_lt q b <=> poly_infnorm_le q (b - 1)
  by rewrite /poly_infnorm_lt /poly_infnorm_le; smt().
by apply poly_infnorm_le_iff; smt().
qed.

(* ==================================================================== *)
(* Vectors over polyXnD1.                                                *)
(*                                                                      *)
(* Clones DynMatrix at the polyXnD1 polynomial ring, then defines       *)
(* entry-wise centered-inf-norm bound predicates and a computed         *)
(* inf-norm on vectors, with soundness lemmas tying the two.            *)
(* (Matrix-level can be added analogously in a follow-up.)              *)
(* ==================================================================== *)

clone import DynMatrix as VM with
  theory ZR <- ComRingDflInv.
import VM.Vectors.

(* -------------------------------------------------------------------- *)
(* Vector-level: entry-wise centered-inf-norm predicates.                *)

op vec_infnorm_lt (v : vector) (b : int) : bool =
  forall i, 0 <= i < size v => poly_infnorm_lt v.[i] b.

op vec_infnorm_le (v : vector) (b : int) : bool =
  forall i, 0 <= i < size v => poly_infnorm_le v.[i] b.

(* -------------------------------------------------------------------- *)
(* Computed vector inf-norm via big-max of per-entry inf-norms.          *)

op inf_normv (v : vector) : Nneg.nneg =
  Nneg.BMaxN.bigi predT (fun i => inf_norm v.[i]) 0 (size v).

(* -------------------------------------------------------------------- *)
(* Soundness: vector-level [_le] check iff the computed vector inf-norm *)
(* is bounded by [Nneg.ofint b].                                        *)

lemma vec_infnorm_le_iff (v : vector) (b : int) :
  0 <= b =>
  (vec_infnorm_le v b <=> Nneg.(<=) (inf_normv v) (Nneg.ofint b)).
proof.
move=> ge0_b; rewrite /vec_infnorm_le /inf_normv Nneg.BMaxN.big_le_iff.
split.
- move=> H; split; first by apply Nneg.zero_le.
  move=> i; rewrite mem_range => Hi _ /=.
  have := H i _; first by smt().
  by rewrite -(poly_infnorm_le_iff _ _ ge0_b).
- case=> _ H i Hi.
  have Hi' : i \in range 0 (size v) by rewrite mem_range; smt().
  have := H i Hi' _; first by [].
  by rewrite /= -(poly_infnorm_le_iff _ _ ge0_b).
qed.

lemma vec_infnorm_lt_iff (v : vector) (b : int) :
  1 <= b =>
  (vec_infnorm_lt v b <=> Nneg.(<=) (inf_normv v) (Nneg.ofint (b - 1))).
proof.
move=> ge1_b.
have -> : vec_infnorm_lt v b <=> vec_infnorm_le v (b - 1).
- rewrite /vec_infnorm_lt /vec_infnorm_le.
  split=> H i Hi; have := H i Hi.
  + by rewrite /poly_infnorm_lt /poly_infnorm_le; smt().
  + by rewrite /poly_infnorm_lt /poly_infnorm_le; smt().
by apply vec_infnorm_le_iff; smt().
qed.

(* -------------------------------------------------------------------- *)
(* Matrix-level: entry-wise centered-inf-norm predicates and norm.       *)
import VM.Matrices.

op mat_infnorm_lt (m : matrix) (b : int) : bool =
  forall i j, 0 <= i < rows m => 0 <= j < cols m =>
    poly_infnorm_lt m.[(i, j)] b.

op mat_infnorm_le (m : matrix) (b : int) : bool =
  forall i j, 0 <= i < rows m => 0 <= j < cols m =>
    poly_infnorm_le m.[(i, j)] b.

op inf_normm (m : matrix) : Nneg.nneg =
  Nneg.BMaxN.bigi predT
    (fun i => Nneg.BMaxN.bigi predT
                (fun j => inf_norm m.[(i, j)]) 0 (cols m))
    0 (rows m).

lemma mat_infnorm_le_iff (m : matrix) (b : int) :
  0 <= b =>
  (mat_infnorm_le m b <=> Nneg.(<=) (inf_normm m) (Nneg.ofint b)).
proof.
move=> ge0_b; rewrite /mat_infnorm_le /inf_normm Nneg.BMaxN.big_le_iff.
split.
- move=> H; split; first by apply Nneg.zero_le.
  move=> i; rewrite mem_range => Hi _ /=.
  rewrite Nneg.BMaxN.big_le_iff; split; first by apply Nneg.zero_le.
  move=> j; rewrite mem_range => Hj _ /=.
  by rewrite -(poly_infnorm_le_iff _ _ ge0_b); apply H; smt().
- case=> _ H i j Hi Hj.
  have Hi' : i \in range 0 (rows m) by rewrite mem_range; smt().
  have := H i Hi' _; first by [].
  rewrite /= Nneg.BMaxN.big_le_iff => -[_ Hr].
  have Hj' : j \in range 0 (cols m) by rewrite mem_range; smt().
  have := Hr j Hj' _; first by [].
  by rewrite /= -(poly_infnorm_le_iff _ _ ge0_b).
qed.

lemma mat_infnorm_lt_iff (m : matrix) (b : int) :
  1 <= b =>
  (mat_infnorm_lt m b <=> Nneg.(<=) (inf_normm m) (Nneg.ofint (b - 1))).
proof.
move=> ge1_b.
have -> : mat_infnorm_lt m b <=> mat_infnorm_le m (b - 1).
- rewrite /mat_infnorm_lt /mat_infnorm_le.
  split=> H i j Hi Hj; have := H i j Hi Hj.
  + by rewrite /poly_infnorm_lt /poly_infnorm_le; smt().
  + by rewrite /poly_infnorm_lt /poly_infnorm_le; smt().
by apply mat_infnorm_le_iff; smt().
qed.

end PolyReduceZpCentered.

(* ==================================================================== *)
(* Field version: when [p] is prime, additionally make available the    *)
(* prime-only coefficient lemmas (creprN, creprND, creprN2) on the same *)
(* polyXnD1 coefficient instantiation.                                  *)
(* ==================================================================== *)
abstract theory PolyReduceZpCenteredField.

clone include ZpCenteredField.

clone include PolyReduceZp with
  theory Zp <- ZMR.
import PolyReduce.
import ZMR.
import ZMF.

(* ==================================================================== *)
(* Centered-representation infinity-norm machinery on polyXnD1.         *)
(* (Duplicated from [PolyReduceZpCentered] — both theories provide the  *)
(*  same inf-norm surface on top of their respective coefficient rings.)*)
(* ==================================================================== *)

op poly_infnorm_lt (q : polyXnD1) (b : int) : bool =
  forall i, 0 <= i < n => `|q.[i]| < b.

op poly_infnorm_le (q : polyXnD1) (b : int) : bool =
  forall i, 0 <= i < n => `|q.[i]| <= b.

lemma poly_infnorm_lt_le (q : polyXnD1) (b : int) :
  poly_infnorm_lt q b => poly_infnorm_le q b.
proof. by move=> H i Hi; have := H i Hi; smt(). qed.

lemma poly_infnorm_le_mono (q : polyXnD1) (b1 b2 : int) :
  b1 <= b2 => poly_infnorm_le q b1 => poly_infnorm_le q b2.
proof. by move=> Hb H i Hi; have := H i Hi; smt(). qed.

lemma poly_infnorm_lt_mono (q : polyXnD1) (b1 b2 : int) :
  b1 <= b2 => poly_infnorm_lt q b1 => poly_infnorm_lt q b2.
proof. by move=> Hb H i Hi; have := H i Hi; smt(). qed.

lemma poly_infnorm_le_ub (q : polyXnD1) :
  poly_infnorm_le q (p %/ 2)
  by move=> i Hi; smt(abs_zp_ub).

lemma poly_infnorm_le_zero :
  poly_infnorm_le zeroXnD1 0.
proof. move=> i Hi; rewrite rcoeff0; smt(abs_zp_zero). qed.

lemma poly_infnorm_le_add (q r : polyXnD1) (bq br : int) :
     poly_infnorm_le q bq
  => poly_infnorm_le r br
  => poly_infnorm_le (q + r) (bq + br).
proof.
move=> Hq Hr i Hi.
rewrite rcoeffD; have := abs_zp_triangle q.[i] r.[i].
have := Hq i Hi; have := Hr i Hi; smt().
qed.

lemma poly_infnorm_lt_add (q r : polyXnD1) (bq br : int) :
     poly_infnorm_lt q bq
  => poly_infnorm_lt r br
  => poly_infnorm_lt (q + r) (bq + br).
proof.
move=> Hq Hr i Hi.
rewrite rcoeffD; have := abs_zp_triangle q.[i] r.[i].
have := Hq i Hi; have := Hr i Hi; smt().
qed.

lemma poly_infnorm_le_opp (q : polyXnD1) (b : int) :
  poly_infnorm_le q b => poly_infnorm_le (- q) b.
proof.
move=> H i Hi.
rewrite -rcoeffN -abs_zpN.
have := H i Hi; smt().
qed.

lemma poly_infnorm_lt_opp (q : polyXnD1) (b : int) :
  poly_infnorm_lt q b => poly_infnorm_lt (- q) b.
proof.
move=> H i Hi.
rewrite -rcoeffN -abs_zpN.
have := H i Hi; smt().
qed.

op inf_norm (q : polyXnD1) : Nneg.nneg =
  Nneg.BMaxN.bigi predT (fun i => Nneg.ofint `|q.[i]|) 0 n.

lemma poly_infnorm_le_iff (q : polyXnD1) (b : int) :
  0 <= b =>
  (poly_infnorm_le q b <=> Nneg.(<=) (inf_norm q) (Nneg.ofint b)).
proof.
move=> ge0_b; rewrite /poly_infnorm_le /inf_norm Nneg.BMaxN.big_le_iff.
have valK_b : Nneg.val (Nneg.ofint b) = b by apply Nneg.valK_pos.
have step : forall a, 0 <= a =>
  Nneg.(<=) (Nneg.ofint a) (Nneg.ofint b) <=> a <= b.
- move=> a ge0_a; rewrite /Nneg.(<=) valK_b.
  by have -> : Nneg.val (Nneg.ofint a) = a by apply Nneg.valK_pos.
split.
- move=> H; split; first by apply Nneg.zero_le.
  move=> i; rewrite mem_range => Hi _ /=.
  have ge0_a : 0 <= `|q.[i]| by smt().
  by rewrite step //; apply H; smt().
- case=> _ H i Hi.
  have Hi' : i \in range 0 n by rewrite mem_range; smt().
  have ge0_a : 0 <= `|q.[i]| by smt().
  have := H i Hi' _; first by [].
  by rewrite /= step.
qed.

lemma poly_infnorm_lt_iff (q : polyXnD1) (b : int) :
  1 <= b =>
  (poly_infnorm_lt q b <=> Nneg.(<=) (inf_norm q) (Nneg.ofint (b - 1))).
proof.
move=> ge1_b.
have -> : poly_infnorm_lt q b <=> poly_infnorm_le q (b - 1)
  by rewrite /poly_infnorm_lt /poly_infnorm_le; smt().
by apply poly_infnorm_le_iff; smt().
qed.

(* -------------------------------------------------------------------- *)
(* Vector / Matrix layer.                                                *)

clone import DynMatrix as VM with
  theory ZR <- ComRingDflInv.
import VM.Vectors.

op vec_infnorm_lt (v : vector) (b : int) : bool =
  forall i, 0 <= i < size v => poly_infnorm_lt v.[i] b.

op vec_infnorm_le (v : vector) (b : int) : bool =
  forall i, 0 <= i < size v => poly_infnorm_le v.[i] b.

op inf_normv (v : vector) : Nneg.nneg =
  Nneg.BMaxN.bigi predT (fun i => inf_norm v.[i]) 0 (size v).

lemma vec_infnorm_le_iff (v : vector) (b : int) :
  0 <= b =>
  (vec_infnorm_le v b <=> Nneg.(<=) (inf_normv v) (Nneg.ofint b)).
proof.
move=> ge0_b; rewrite /vec_infnorm_le /inf_normv Nneg.BMaxN.big_le_iff.
split.
- move=> H; split; first by apply Nneg.zero_le.
  move=> i; rewrite mem_range => Hi _ /=.
  have := H i _; first by smt().
  by rewrite -(poly_infnorm_le_iff _ _ ge0_b).
- case=> _ H i Hi.
  have Hi' : i \in range 0 (size v) by rewrite mem_range; smt().
  have := H i Hi' _; first by [].
  by rewrite /= -(poly_infnorm_le_iff _ _ ge0_b).
qed.

lemma vec_infnorm_lt_iff (v : vector) (b : int) :
  1 <= b =>
  (vec_infnorm_lt v b <=> Nneg.(<=) (inf_normv v) (Nneg.ofint (b - 1))).
proof.
move=> ge1_b.
have -> : vec_infnorm_lt v b <=> vec_infnorm_le v (b - 1).
- rewrite /vec_infnorm_lt /vec_infnorm_le.
  split=> H i Hi; have := H i Hi.
  + by rewrite /poly_infnorm_lt /poly_infnorm_le; smt().
  + by rewrite /poly_infnorm_lt /poly_infnorm_le; smt().
by apply vec_infnorm_le_iff; smt().
qed.

import VM.Matrices.

op mat_infnorm_lt (m : matrix) (b : int) : bool =
  forall i j, 0 <= i < rows m => 0 <= j < cols m =>
    poly_infnorm_lt m.[(i, j)] b.

op mat_infnorm_le (m : matrix) (b : int) : bool =
  forall i j, 0 <= i < rows m => 0 <= j < cols m =>
    poly_infnorm_le m.[(i, j)] b.

op inf_normm (m : matrix) : Nneg.nneg =
  Nneg.BMaxN.bigi predT
    (fun i => Nneg.BMaxN.bigi predT
                (fun j => inf_norm m.[(i, j)]) 0 (cols m))
    0 (rows m).

lemma mat_infnorm_le_iff (m : matrix) (b : int) :
  0 <= b =>
  (mat_infnorm_le m b <=> Nneg.(<=) (inf_normm m) (Nneg.ofint b)).
proof.
move=> ge0_b; rewrite /mat_infnorm_le /inf_normm Nneg.BMaxN.big_le_iff.
split.
- move=> H; split; first by apply Nneg.zero_le.
  move=> i; rewrite mem_range => Hi _ /=.
  rewrite Nneg.BMaxN.big_le_iff; split; first by apply Nneg.zero_le.
  move=> j; rewrite mem_range => Hj _ /=.
  by rewrite -(poly_infnorm_le_iff _ _ ge0_b); apply H; smt().
- case=> _ H i j Hi Hj.
  have Hi' : i \in range 0 (rows m) by rewrite mem_range; smt().
  have := H i Hi' _; first by [].
  rewrite /= Nneg.BMaxN.big_le_iff => -[_ Hr].
  have Hj' : j \in range 0 (cols m) by rewrite mem_range; smt().
  have := Hr j Hj' _; first by [].
  by rewrite /= -(poly_infnorm_le_iff _ _ ge0_b).
qed.

lemma mat_infnorm_lt_iff (m : matrix) (b : int) :
  1 <= b =>
  (mat_infnorm_lt m b <=> Nneg.(<=) (inf_normm m) (Nneg.ofint (b - 1))).
proof.
move=> ge1_b.
have -> : mat_infnorm_lt m b <=> mat_infnorm_le m (b - 1).
- rewrite /mat_infnorm_lt /mat_infnorm_le.
  split=> H i j Hi Hj; have := H i j Hi Hj.
  + by rewrite /poly_infnorm_lt /poly_infnorm_le; smt().
  + by rewrite /poly_infnorm_lt /poly_infnorm_le; smt().
by apply mat_infnorm_le_iff; smt().
qed.

end PolyReduceZpCenteredField.
