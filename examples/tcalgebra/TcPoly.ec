(* -------------------------------------------------------------------- *)
require import AllCore Finite Distr DList List IntMin StdBigop StdOrder.
require Subtype.
require import TcMonoid TcRing TcBigop TcBigalg TcInt.
(*---*) import Bigint IntOrder.

(* ==================================================================== *)
(* Univariate polynomials over a [comring] coefficient algebra. Mirrors *)
(* [theories/algebra/Poly.ec:PolyComRing] but as a section over [c]    *)
(* with TC instances accumulating: once [poly : addgroup] is registered *)
(* in Phase 3, every [bigA] / [bigZModule] lemma applies to polynomial  *)
(* sums; once [poly : comring] in Phase 5, every [bigA]/[bigM] lemma   *)
(* in TcBigalg applies. No "BigPoly" clone needed.                     *)
(* ==================================================================== *)

section.
declare type c <: comring.

(* -------------------------------------------------------------------- *)
(* prepoly = sequence-of-coeffs predicate; poly = subtype thereof      *)
(* -------------------------------------------------------------------- *)
type prepoly = int -> c.

op ispoly (p : prepoly) =
     (forall i, i < 0 => p i = zero<:c>)
  /\ (exists d, forall i, d < i => p i = zero<:c>).

subtype poly = { p : prepoly | ispoly p }
  rename "to_poly", "of_poly".

realize inhabited.
proof. by exists (fun _ => zero<:c>). qed.

(* -------------------------------------------------------------------- *)
op "_.[_]" (p : poly) (i : int) = (of_poly p) i.

lemma lt0_coeff p i : i < 0 => p.[i] = zero<:c>.
proof.
by move=> lt0_i; rewrite /"_.[_]"; case: (of_polyP p) => /(_ _ lt0_i).
qed.

(* -------------------------------------------------------------------- *)
(* Degree machinery                                                    *)
(* -------------------------------------------------------------------- *)
op deg (p : poly) =
  argmin idfun (fun i => forall j, i <= j => p.[j] = zero<:c>).

lemma degP p i :
     0 < i
  => p.[i-1] <> zero<:c>
  => (forall j, i <= j => p.[j] = zero<:c>)
  => deg p = i.
proof.
move=> ge0_i nz_p_iB1 degi @/deg; apply: argmin_eq => /=.
- by apply/ltrW. - by apply: degi.
move=> j [ge0_j lt_ji]; rewrite negb_forall /=.
by exists (i-1); apply/negP => /(_ _); first by move=> /#.
qed.

lemma deg_leP p i : 0 <= i =>
  (forall j, i <= j => p.[j] = zero<:c>) => deg p <= i.
proof.
move=> ge0_i; apply: contraLR; rewrite lerNgt /= => lei.
by have @{1}/deg /argmin_min /=: 0 <= i < deg p by done.
qed.

lemma gedeg_coeff (p : poly) (i : int) : deg p <= i => p.[i] = zero<:c>.
proof.
move=> le_p_i; pose P p i := forall j, i <= j => p.[j] = zero<:c>.
case: (of_polyP p) => [_ [d hd]]; move: (argminP idfun (P p)).
move/(_ (max (d+1) 0) _ _) => /=; first exact: maxrr.
- by move=> j le_d_j; apply: hd => /#.
by apply; apply: le_p_i.
qed.

lemma ge0_deg p : 0 <= deg p.
proof. rewrite /deg &(ge0_argmin). qed.

(* -------------------------------------------------------------------- *)
abbrev lc (p : poly) = p.[deg p - 1].

(* -------------------------------------------------------------------- *)
(* prepoly-level constructors                                           *)
(* -------------------------------------------------------------------- *)
op prepolyC  (a   : c   ) : prepoly = fun i => if i = 0 then a else zero<:c>.
op prepolyXn (k   : int ) : prepoly = fun i => if 0 <= k /\ i = k then oner<:c> else zero<:c>.
op prepolyD  (p q : poly) : prepoly = fun i => p.[i] + q.[i].
op prepolyN  (p   : poly) : prepoly = fun i => - p.[i].

op prepolyM (p q : poly) : prepoly = fun k =>
  bigiA<:c> predT (fun i => p.[i] * q.[k-i]) 0 (k+1).

op prepolyZ (z : c) (p : poly) : prepoly = fun k =>
  z * p.[k].

(* -------------------------------------------------------------------- *)
(* ispoly closure                                                       *)
(* -------------------------------------------------------------------- *)
lemma ispolyC (a : c) : ispoly (prepolyC a).
proof.
split=> @/prepolyC [c' ?|]; first by rewrite ltr_eqF.
by exists 0 => c' gt1_c'; rewrite gtr_eqF.
qed.

lemma ispolyXn (k : int) : ispoly (prepolyXn k).
proof.
split=> @/prepolyXn [c' lt0_c|].
+ by case: (0 <= k) => //= ge0_k; rewrite ltr_eqF //#.
+ by exists k => c' gt1_c'; rewrite gtr_eqF.
qed.

lemma ispolyN (p : poly) : ispoly (prepolyN p).
proof.
split=> @/prepolyN [c' lt0_c|]; first by rewrite oppr_eq0 lt0_coeff.
by exists (deg p) => c' => /ltrW /gedeg_coeff ->; rewrite oppr0.
qed.

lemma ispolyD (p q : poly) : ispoly (prepolyD p q).
proof.
split=> @/prepolyD [c' lt0_c|]; first by rewrite !lt0_coeff // addr0.
by exists (1 + max (deg p) (deg q)) => c' le; rewrite !gedeg_coeff ?addr0 //#.
qed.

lemma ispolyM (p q : poly) : ispoly (prepolyM p q).
proof.
split => @/prepolyM [c' lt0_c|]; 1: by rewrite big_geq //#.
exists (deg p + deg q + 1) => c' ltc; rewrite big_seq big1 //= => i.
rewrite mem_range => -[gt0_i lt_ic]; case: (p.[i] = zero<:c>).
- by move=> ->; rewrite mul0r.
move/(contra _ _ (gedeg_coeff p i)); rewrite lerNgt /= => lt_ip.
by rewrite mulrC gedeg_coeff ?mul0r //#.
qed.

lemma ispolyZ z p : ispoly (prepolyZ z p).
proof.
split => @/prepolyZ [c' lt0_c|]; 1: by rewrite lt0_coeff //mulr0.
by exists (deg p + 1) => c' gtc; rewrite gedeg_coeff ?mulr0 //#.
qed.

lemma poly_eqP (p q : poly) : p = q <=> (forall i, 0 <= i => p.[i] = q.[i]).
proof.
split=> [->//|eq_coeff]; apply/of_poly_inj/fun_ext => i.
case: (i < 0) => [lt0_i|/lerNgt /=]; last by apply: eq_coeff.
by rewrite -/"_.[_]" !lt0_coeff.
qed.

(* -------------------------------------------------------------------- *)
(* poly-level constructors                                              *)
(* -------------------------------------------------------------------- *)
op polyC  a   = to_polyd (prepolyC  a).
op polyXn k   = to_polyd (prepolyXn k).
op polyN  p   = to_polyd (prepolyN  p).
op polyD  p q = to_polyd (prepolyD  p q).
op polyM  p q = to_polyd (prepolyM p q).
op polyZ  z p = to_polyd (prepolyZ z p).

abbrev poly0  : poly = polyC  zero<:c>.
abbrev poly1  : poly = polyC  oner<:c>.
abbrev polyX  : poly = polyXn 1.
abbrev X      : poly = polyXn 1.
abbrev ( + ) (p q : poly) : poly = polyD p q.
abbrev [ - ] (p   : poly) : poly = polyN p.
abbrev ( * ) (p q : poly) : poly = polyM p q.
abbrev ( ** ) z (p : poly) : poly = polyZ z p.

abbrev ( - ) (p q : poly) : poly = p + (-q).

(* -------------------------------------------------------------------- *)
(* Coefficient formulas                                                 *)
(* -------------------------------------------------------------------- *)
lemma coeffE p k : ispoly p => (to_polyd p).[k] = p k.
proof. by move=> ?; rewrite /"_.[_]" to_polydK. qed.

lemma polyCE a k : (polyC a).[k] = if k = 0 then a else zero<:c>.
proof. by rewrite coeffE 1:ispolyC. qed.

lemma polyXE k : X.[k] = if k = 1 then oner<:c> else zero<:c>.
proof. by rewrite coeffE 1:ispolyXn. qed.

lemma poly0E k : poly0.[k] = zero<:c>.
proof. by rewrite polyCE if_same. qed.

lemma polyNE p k : (-p).[k] = - p.[k].
proof. by rewrite coeffE 1:ispolyN. qed.

lemma polyDE p q k : (p + q).[k] = p.[k] + q.[k].
proof. by rewrite coeffE 1:ispolyD. qed.

lemma polyME p q k : (p * q).[k] =
  bigiA<:c> predT (fun i => p.[i] * q.[k-i]) 0 (k+1).
proof. by rewrite coeffE 1:ispolyM. qed.

lemma polyMXE p k : (p * X).[k] = p.[k-1].
proof.
case: (k < 0) => [lt0_k|]; first by rewrite !lt0_coeff //#.
rewrite ltrNge => /= ge0_k; rewrite polyME; move: ge0_k.
rewrite ler_eqVlt => -[<-|gt0_k] /=.
- by rewrite big_int1 /= polyXE /= mulr0 lt0_coeff.
rewrite (@bigD1<:c, int> _ _ (k-1)) ?mem_range 1:/# 1:range_uniq /=.
rewrite opprB addrCA /= polyXE /= mulr1 big1 // ?addr0 //.
move=> i @/predC1 nei /=; rewrite polyXE.
case: (k - i = 1) => [/#|_ /=]; first by rewrite mulr0.
qed.

lemma polyZE z p k : (z ** p).[k] = z * p.[k].
proof. by rewrite coeffE 1:ispolyZ. qed.

hint rewrite coeffpE : poly0E polyDE polyNE polyME polyZE.

(* -------------------------------------------------------------------- *)
(* polyC properties                                                     *)
(* -------------------------------------------------------------------- *)
lemma polyCN (a : c) : polyC (- a) = - (polyC a).
proof.
apply/poly_eqP=> i ge0_i; rewrite !(coeffpE, polyCE).
by case: (i = 0) => // _; rewrite oppr0.
qed.

lemma polyCD (a1 a2 : c) : polyC (a1 + a2) = polyC a1 + polyC a2.
proof.
apply/poly_eqP=> i ge0_i; rewrite !(coeffpE, polyCE).
by case: (i = 0) => // _; rewrite addr0.
qed.

lemma polyCM (a1 a2 : c) : polyC (a1 * a2) = polyC a1 * polyC a2.
proof.
apply/poly_eqP=> i ge0_i; rewrite !(coeffpE, polyCE).
case: (i = 0) => [->|ne0_i]; first by rewrite big_int1 /= !polyCE.
rewrite big_seq big1 ?addr0 //= => j /mem_range rg_j.
rewrite !polyCE; case: (j = 0) => [->>/=|]; last by rewrite mul0r.
by rewrite ne0_i /= mulr0.
qed.

(* -------------------------------------------------------------------- *)
(* ZModule axioms on poly. Mirrors original [clone Ring.ZModule as     *)
(* ZPoly] but as standalone lemmas; will feed into the [addgroup]      *)
(* instance in Phase 3.                                                *)
(* -------------------------------------------------------------------- *)
lemma polyD_addrA (p q r : poly) : p + (q + r) = (p + q) + r.
proof. by apply/poly_eqP=> i ge0_i; rewrite !coeffpE addrA. qed.

lemma polyD_addrC (p q : poly) : p + q = q + p.
proof. by apply/poly_eqP=> i ge0_i; rewrite !coeffpE addrC. qed.

lemma polyD_add0r (p : poly) : poly0 + p = p.
proof. by apply/poly_eqP=> i ge0_i; rewrite !coeffpE add0r. qed.

lemma polyD_addNr (p : poly) : (-p) + p = poly0.
proof. by apply/poly_eqP=> i ge0_i; rewrite !coeffpE addNr. qed.

(* -------------------------------------------------------------------- *)
(* Scaling lemmas                                                       *)
(* -------------------------------------------------------------------- *)
lemma scale0p p : zero<:c> ** p = poly0.
proof. by apply/poly_eqP=> i ge0_i; rewrite !coeffpE mul0r. qed.

lemma scalep0 a : a ** poly0 = poly0.
proof. by apply/poly_eqP=> i ge0_i; rewrite !coeffpE mulr0. qed.

lemma scale1p p : oner<:c> ** p = p.
proof. by apply/poly_eqP=> i ge0_i; rewrite !coeffpE mul1r. qed.

lemma scalep1 (a : c) : a ** poly1 = polyC a.
proof.
apply/poly_eqP=> i ge0_i; rewrite !coeffpE !polyCE.
by case: (i = 0) => _; [rewrite mulr1|rewrite mulr0].
qed.

lemma scaleNp (a : c) p : (-a) ** p = - (a ** p).
proof. by apply/poly_eqP=> i ge0_i; rewrite !coeffpE mulNr. qed.

lemma scalepN (a : c) p : a ** (-p) = - (a ** p).
proof. by apply/poly_eqP=> i ge0_i; rewrite !coeffpE mulrN. qed.

lemma scalepA (a1 a2 : c) p : a1 ** (a2 ** p) = (a1 * a2) ** p.
proof. by apply/poly_eqP=> i ge0_i; rewrite !coeffpE mulrA. qed.

lemma scalepDr (a : c) p q : a ** (p + q) = (a ** p) + (a ** q).
proof. by apply/poly_eqP=> i ge0_i; rewrite !coeffpE mulrDr. qed.

lemma scalepBr (a : c) p q : a ** (p - q) = (a ** p) - (a ** q).
proof. by rewrite scalepDr scalepN. qed.

lemma scalepDl (a1 a2 : c) p : (a1 + a2) ** p = (a1 ** p) + (a2 ** p).
proof. by apply/poly_eqP=> i ge0_i; rewrite !coeffpE mulrDl. qed.

lemma scalepBl (a1 a2 : c) p : (a1 - a2) ** p = (a1 ** p) - (a2 ** p).
proof. by rewrite scalepDl scaleNp. qed.

lemma scalepE (a : c) p : a ** p = polyC a * p.
proof.
apply/poly_eqP=> i ge0_i; rewrite !coeffpE /=.
rewrite big_int_recl //= polyCE /=.
rewrite big_seq big1 ?addr0 //= => j /mem_range.
by case=> ge0_j _; rewrite polyCE addz1_neq0 //= mul0r.
qed.

(* -------------------------------------------------------------------- *)
(* Multiplication: extended coefficient formulas, then the ComRing      *)
(* axioms (associativity / commutativity / unit / distributivity).      *)
(* Mirrors original [Poly.ec] lines 418-498.                            *)
(* -------------------------------------------------------------------- *)
lemma polyMEw M p q k : k <= M =>
  (p * q).[k] = bigiA<:c> predT (fun i => p.[i] * q.[k-i]) 0 (M+1).
proof.
move=> le_kM; case: (k < 0) => [lt0_k|/lerNgt ge0_k].
+ rewrite lt0_coeff // big_seq big1 //= => i.
  by case/mem_range=> [ge0_i lt_iM]; rewrite (lt0_coeff q) ?mulr0 //#.
rewrite (@big_cat_int (k+1)) 1,2:/# -polyME.
rewrite big_seq big1 2:addr0 //= => i /mem_range.
by case=> [lt_ki lt_iM]; rewrite (lt0_coeff q) ?mulr0 //#.
qed.

lemma polyM_mulrC : commutative polyM.
proof.
move=> p q; apply: poly_eqP => k ge0_k; rewrite !polyME.
pose F j := k - j; rewrite (@big_reindex _ _ F F) 1:/#.
rewrite predT_comp /(\o) /=; pose s := map _ _.
apply: (eq_trans _ _ _ (eq_big_perm _ _ _ (range 0 (k+1)) _)).
+ rewrite uniq_perm_eq 2:&(range_uniq) /s.
  * rewrite map_inj_in_uniq 2:&(range_uniq) => x y.
    by rewrite !mem_range /F /#.
  * move=> x; split => [/mapP[y []]|]; 1: by rewrite !mem_range /#.
    rewrite !mem_range => *; apply/mapP; exists (F x).
    by rewrite !mem_range /F /#.
+ by apply: eq_bigr => /= i _ @/F; rewrite mulrC /#.
qed.

lemma polyMEwr M p q k : k <= M =>
  (p * q).[k] = bigiA<:c> predT (fun i => p.[k-i] * q.[i]) 0 (M+1).
proof.
rewrite -{1}polyM_mulrC => /polyMEw ->; apply: eq_bigr.
by move=> i _ /=; rewrite mulrC.
qed.

lemma polyMEr p q k :
  (p * q).[k] = bigiA<:c> predT (fun i => p.[k-i] * q.[i]) 0 (k+1).
proof. by rewrite (@polyMEwr k). qed.

lemma polyM_mulrA : associative polyM.
proof.
move=> p q r; apply: poly_eqP => k ge0_k.
have ->: (p * (q * r)).[k] =
  bigiA<:c> predT (fun i =>
    bigiA<:c> predT (fun j => p.[i] * q.[k - i - j] * r.[j]) 0 (k+1)
  ) 0 (k+1).
+ rewrite polyME !big_seq &(eq_bigr) => /= i.
  case/mem_range => g0_i lt_i_Sk; rewrite (@polyMEwr k) 1:/#.
  by rewrite mulr_sumr &(eq_bigr) => /= j _; rewrite mulrA.
have ->: ((p * q) * r).[k] =
  bigiA<:c> predT (fun i =>
    bigiA<:c> predT (fun j => p.[j] * q.[k - i - j] * r.[i]) 0 (k+1)
  ) 0 (k+1).
+ rewrite polyMEr !big_seq &(eq_bigr) => /= i.
  case/mem_range => ge0_i lt_i_Sk; rewrite (@polyMEw k) 1:/#.
  by rewrite mulr_suml &(eq_bigr).
rewrite exchange_big &(eq_bigr) => /= i _.
by rewrite &(eq_bigr) => /= j _ /#.
qed.

lemma polyM_mul1r : left_id poly1 polyM.
proof.
move=> p; apply: poly_eqP => i ge0_i.
rewrite polyME big_int_recl //= polyCE /= mul1r.
rewrite big_seq big1 -1:?addr0 //=.
move=> j; rewrite mem_range=> -[ge0_j _]; rewrite polyCE.
by rewrite addz1_neq0 //= mul0r.
qed.

lemma polyM_mul0r p : poly0 * p = poly0.
proof.
apply/poly_eqP=> i _; rewrite poly0E polyME.
by rewrite big1 //= => j _; rewrite poly0E mul0r.
qed.

lemma polyM_mulrDl : left_distributive polyM polyD.
proof.
move=> p q r; apply: poly_eqP => i ge0_i; rewrite !(polyME, polyDE).
by rewrite -big_split &(eq_bigr) => /= j _; rewrite polyDE mulrDl.
qed.

lemma polyM_oner_neq0 : poly1 <> poly0.
proof. by apply/negP => /poly_eqP /(_ 0); rewrite !polyCE /= oner_neq0<:c>. qed.

end section.

(* -------------------------------------------------------------------- *)
(* Wrappers needed by [instance]: its [op X = name] clause requires a *)
(* qualified ident on the rhs (not an [abbrev]).                        *)
(* -------------------------------------------------------------------- *)
op poly_zero ['c <: comring] : 'c poly = polyC zero<:'c>.
op poly_one  ['c <: comring] : 'c poly = polyC oner<:'c>.

(* ==================================================================== *)
(* Phase 3: register [poly] as an [addgroup] over a [comring]           *)
(* coefficient. Once this lands, every [bigA] / [bigZModule] lemma      *)
(* polymorphic over [addmonoid] applies at carrier ['c poly].           *)
(* ==================================================================== *)
instance addgroup with ['c <: comring] ('c poly)
  op idm   = poly_zero<:'c>
  op (+)   = polyD<:'c>
  op [-]   = polyN<:'c>

  proof addmA by apply polyD_addrA
  proof addmC by apply polyD_addrC
  proof add0m by (move=> p; rewrite -/(poly_zero<:'c>); apply polyD_add0r)
  proof addrN by (move=> p; rewrite polyD_addrC -/(poly_zero<:'c>); apply polyD_addNr).

(* ==================================================================== *)
(* Phase 5: register [poly] as a [comring] over a [comring] coefficient.*)
(* Mirrors [Ring.ec:ComRingDflInv]: when no structural inverse is       *)
(* available (here, because the structural "constant with invertible    *)
(* coefficient" characterisation only holds when [c] has no zero        *)
(* divisors, i.e. [c : idomain]), use [choiceb] to pick a left inverse  *)
(* if any exists, fall back to the element itself otherwise. The three  *)
(* obligations [mulVr] / [unitP] / [unitout] discharge from [choicebP]  *)
(* and [choiceb_dfl] alone — no ring axioms needed.                     *)
(* ==================================================================== *)
op poly_unit ['c <: comring] (p : 'c poly) : bool =
  exists q, polyM q p = poly_one<:'c>.

op poly_invr ['c <: comring] (p : 'c poly) : 'c poly =
  choiceb (fun q => polyM q p = poly_one<:'c>) p.

instance comring with ['c <: comring] ('c poly)
  op idm   = poly_zero<:'c>
  op (+)   = polyD<:'c>
  op [-]   = polyN<:'c>
  op oner  = poly_one<:'c>
  op ( * ) = polyM<:'c>
  op invr  = poly_invr<:'c>
  op unit  = poly_unit<:'c>

  proof addmA      by apply polyD_addrA
  proof addmC      by apply polyD_addrC
  proof add0m      by (move=> p; rewrite -/(poly_zero<:'c>); apply polyD_add0r)
  proof addrN      by (move=> p; rewrite polyD_addrC -/(poly_zero<:'c>); apply polyD_addNr)
  proof oner_neq0  by (rewrite -/(poly_one<:'c>) -/(poly_zero<:'c>); apply polyM_oner_neq0)
  proof mulrA      by apply polyM_mulrA
  proof mulrC      by apply polyM_mulrC
  proof mul1r      by (move=> p; rewrite -/(poly_one<:'c>); apply polyM_mul1r)
  proof mulrDl     by apply polyM_mulrDl
  proof mulVr      by (move=> p hu; rewrite /poly_invr<:'c>;
                       have := choicebP (fun q => polyM q p = poly_one<:'c>) p hu;
                       by rewrite /=)
  proof unitP      by (move=> p q heq; rewrite /poly_unit<:'c>; by exists q)
  proof unitout    by (move=> p; rewrite /poly_unit<:'c> /poly_invr<:'c> negb_exists => hne;
                       by apply choiceb_dfl => q; apply hne).

(* ==================================================================== *)
(* Phase 6: higher-level theory of polynomials over a [comring]        *)
(* coefficient. Mirrors [theories/algebra/Poly.ec] from [degC]         *)
(* (line 296) onwards: degree arithmetic, multiplicative degree,       *)
(* X^i / polyXn, polysumE / polyE / polywE, peval, polyL constructor.  *)
(* ==================================================================== *)
section.
declare type c <: comring.

(* -------------------------------------------------------------------- *)
(* Degree of constants, leading coefficient, [poly0]/[poly1] degrees.  *)
(* -------------------------------------------------------------------- *)
lemma degC (a : c) : deg (polyC a) = if a = zero<:c> then 0 else 1.
proof.
case: (a = zero<:c>) => [->|nz_a]; last first.
- apply: degP => //=; first by rewrite polyCE.
  by move=> i ge1_i; rewrite polyCE gtr_eqF //#.
rewrite /deg; apply: argmin_eq => //=.
- by move=> j _; rewrite poly0E.
- by move=> j; apply: contraL => _ /#.
qed.

lemma degC_le (a : c) : deg (polyC a) <= 1.
proof. by rewrite degC; case: (a = zero<:c>). qed.

lemma lcC (a : c) : lc (polyC a) = a.
proof. by rewrite polyCE degC; case: (a = zero<:c>) => [->|]. qed.

lemma lc0 : lc poly0<:c> = zero<:c>.
proof. by apply: lcC. qed.

lemma lc1 : lc poly1<:c> = oner<:c>.
proof. by apply: lcC. qed.

lemma deg0 : deg poly0<:c> = 0.
proof. by rewrite degC. qed.

lemma deg1 : deg poly1<:c> = 1.
proof.
apply: degP => //=; first by rewrite polyCE /= oner_neq0.
by move=> i ge1_i; rewrite polyCE gtr_eqF //#.
qed.

lemma deg_eq0 (p : c poly) : (deg p = 0) <=> (p = poly0).
proof.
split=> [z_degp|->]; last by rewrite deg0.
apply/poly_eqP=> i ge0_i; rewrite poly0E.
by apply/gedeg_coeff; rewrite z_degp.
qed.

lemma degX : deg X<:c> = 2.
proof.
apply/degP=> //=; first by rewrite polyXE /= oner_neq0.
by move=> i ge2_i; rewrite polyXE gtr_eqF //#.
qed.

lemma nz_polyX : X<:c> <> poly0.
proof. by rewrite -deg_eq0 degX. qed.

lemma lcX : lc X<:c> = oner<:c>.
proof. by rewrite degX /= polyXE. qed.

lemma deg_ge1 (p : c poly) : (1 <= deg p) <=> (p <> poly0).
proof. by rewrite -deg_eq0 eqr_le ge0_deg /= (lerNgt _ 0) /#. qed.

lemma deg_gt0 (p : c poly) : (0 < deg p) <=> (p <> poly0).
proof. by rewrite -deg_ge1 /#. qed.

lemma deg_eq1 (p : c poly) :
  (deg p = 1) <=> (exists a, a <> zero<:c> /\ p = polyC a).
proof.
split=> [eq1_degp|[a [nz_a ->>]]]; last first.
+ by apply: degP => //= => [|i ge1_i]; rewrite polyCE //= gtr_eqF /#.
have pC: forall i, 1 <= i => p.[i] = zero<:c>.
+ by move=> i ge1_i; apply: gedeg_coeff; rewrite eq1_degp.
exists p.[0]; split; last first.
+ apply/poly_eqP => i /ler_eqVlt -[<<-|]; first by rewrite polyCE.
  by move=> gt0_i; rewrite polyCE gtr_eqF //= &(pC) /#.
apply: contraL eq1_degp => z_p0; suff ->: p = poly0 by rewrite deg0.
apply/poly_eqP=> i; rewrite poly0E => /ler_eqVlt [<<-//|].
by move=> gt0_i; apply: pC => /#.
qed.

lemma lc_eq0 (p : c poly) : (lc p = zero<:c>) <=> (p = poly0).
proof.
case: (p = poly0) => [->|] /=; first by rewrite lc0.
rewrite -deg_eq0 eqr_le ge0_deg /= -ltrNge => gt0_deg.
pose P i := forall j, (i <= j)%Int => p.[j] = zero<:c>.
apply/negP => zp; have h: 0 <= deg p - 1 < argmin idfun P.
+ rewrite /P /argmin -/(deg p); smt(ge0_deg).
have := argmin_min idfun P (deg p - 1) h.
move=> @/idfun /= j /ler_eqVlt [<<-//| ltj].
by apply: gedeg_coeff => /#.
qed.

(* -------------------------------------------------------------------- *)
(* Degree of additive operations.                                       *)
(* -------------------------------------------------------------------- *)
lemma degN (p : c poly) : deg (-p) = deg p.
proof.
rewrite /deg; congr; apply/fun_ext => /= i; apply/eq_iff.
by split=> + j - /(_ j); rewrite polyNE oppr_eq0.
qed.

lemma lcN (p : c poly) : lc (-p) = - lc p.
proof. by rewrite degN polyNE. qed.

lemma degD (p q : c poly) : deg (p + q) <= max (deg p) (deg q).
proof.
apply: deg_leP; [by smt(ge0_deg) | move=> i /ler_maxrP[le1 le2]].
by rewrite polyDE !gedeg_coeff ?addr0.
qed.

lemma degB (p q : c poly) : deg (p - q) <= max (deg p) (deg q).
proof. by rewrite -(degN q) &(degD). qed.

lemma degDl (p q : c poly) : deg q < deg p => deg (p + q) = deg p.
proof.
move=> le_pq; have gt0_p: 0 < deg p.
- by apply/(ler_lt_trans _ _ _ _ le_pq)/ge0_deg.
apply: degP=> //.
- rewrite polyDE (gedeg_coeff q) 1:/#.
  by rewrite addr0 lc_eq0 -deg_eq0 gtr_eqF.
- move=> i le_pi; rewrite polyDE !gedeg_coeff ?addr0 //.
  by apply/ltrW/(ltr_le_trans _ _ _ le_pq).
qed.

lemma lcDl (p q : c poly) : deg q < deg p => lc (p + q) = lc p.
proof.
move=> ^lt_pq /degDl ->; rewrite polyDE.
by rewrite addrC gedeg_coeff ?add0r //#.
qed.

lemma degDr (p q : c poly) : deg p < deg q => deg (p + q) = deg q.
proof. by move=> h; rewrite (polyD_addrC<:c> p q); apply degDl. qed.

lemma lcDr (p q : c poly) : deg p < deg q => lc (p + q) = lc q.
proof. by move=> h; rewrite (polyD_addrC<:c> p q); apply lcDl. qed.

end section.
