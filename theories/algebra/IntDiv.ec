(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
require import Core Int IntMin Ring StdOrder.
(*---*) import Ring.IntID IntOrder.

(* -------------------------------------------------------------------- *)
lemma nosmt euclide_nat m d : 0 <= m => 0 < d =>
  exists q r, 0 <= r < d /\ m = q * d + r.
proof.
move=> ge0_m gt0_d; elim: m ge0_m => [|m ih] //=; 1: by exists 0 0.
case=> q r [[ge0_r lt_rd] ->]; case: (r + 1 = d) => [SrE|ne_Sr_d].
  exists (q+1) 0 => //=; 1: by rewrite gt0_d -addrA SrE /= mulrDl.
exists q (r+1) => //; rewrite addr_ge0 //= ltr_neqAle ne_Sr_d /=.
by rewrite -ltzE lt_rd addrA.
qed.

(* -------------------------------------------------------------------- *)
op euclidef (m d : int) (qr : int * int) =
     m = qr.`1 * d + qr.`2
  /\ (d <> 0 => 0 <= qr.`2 < `|d|).

op edivn (m d : int) =
  if (d < 0 \/ m < 0) then (0, 0) else
    if d = 0 then (0, m) else choiceb (euclidef m d) (0, 0)
  axiomatized by edivn_def.

op edivz (m d : int) =
  let (q, r) =
    if 0 <= m then edivn m `|d| else
      let (q, r) = edivn (-(m+1)) `|d| in
      (- (q + 1), `|d| - 1 - r)
    in (signz d * q, r)
  axiomatized by edivz_def.

abbrev (%/) (m d : int) = (edivz m d).`1.
abbrev (%%) (m d : int) = (edivz m d).`2.

op (%|) (m d : int) = (d %% m = 0).

(* -------------------------------------------------------------------- *)
lemma nosmt edivnP (m d : int): 0 <= m => 0 <= d =>
  euclidef m d (edivn m d).
proof.
move=> ge0_m ge0_d; rewrite edivn_def !ltrNge !(ge0_m, ge0_d) /=.
case: (d = 0) => [->|] //= nz_d; apply/(choicebP (euclidef m d)).
case: (euclide_nat m d _ _) => //; 1: by rewrite ltr_neqAle eq_sym.
by move=> q r [lt_rd mE]; exists (q, r); rewrite /euclidef ger0_norm.
qed.

(* -------------------------------------------------------------------- *)
lemma nosmt edivzP_r (m d : int): euclidef m d (edivz m d).
proof.
rewrite edivz_def; case: (0 <= m).
+ move=> ge0_m; case _: (edivn _ _) => q r E /=.
  case: (edivnP m `|d| _ _) => //; rewrite ?normr_ge0 E /= => mE.
  rewrite normr0P normr_id => lt_rd; split=> /= [|/lt_rd] //.
  by rewrite mulrAC -signVzE mE mulrC.
rewrite lerNgt /= => lt0_m; case _: (edivn _ _) => q r E /=.
case: (edivnP (-(m+1)) `|d| _ _) => /=; rewrite ?E /=.
  by rewrite oppr_ge0 -ltzE. by rewrite normr_ge0.
rewrite normr0P normr_id=> mE lt_rd; split=> /=; last first.
  move/lt_rd=> {lt_rd}[ge0_r lt_rd]; rewrite -addrA -opprD.
  rewrite subr_ge0 (addrC 1) -ltzE lt_rd /= ltr_snaddr //.
  by rewrite oppr_lt0 ltzS.
apply/(addIr 1)/oppr_inj; rewrite mE; case: (d = 0) => [|nz_d].
  by move=> ->; rewrite normr0 /=.
by rewrite mulrN mulNr -addrA opprD opprK mulrAC -signVzE #ring.
qed.

lemma nosmt edivzP (m d : int) :
  m = (m %/ d) * d + (m %% d) /\ (d <> 0 => 0 <= m %% d < `|d|).
proof. by case: (edivzP_r m d). qed.

(* -------------------------------------------------------------------- *)
lemma nosmt divz0 m: m %/ 0 = 0.
proof.
rewrite edivz_def; case: (0 <= m) => /= _.
  by case: (edivn _ _) => q r /=; rewrite signz0.
by case: (edivn _ _) => q r /=; rewrite signz0.
qed.

lemma nosmt modz0 m: m %% 0 = m.
proof. by have [/= <-] := edivzP m 0. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt euclideU d q q' r r' :
     q * d + r = q' * d + r'
  => 0 <= r  < `|d|
  => 0 <= r' < `|d|
  => q = q' /\ r = r'.
proof.
case: (d = 0) => [->|nz_d]; first by rewrite normr0 ler_lt_asym.
case: (q' = q) => [-> /addrI ->|ne_qq'] //=; rewrite addrC -eqr_sub.
move/(congr1 "`|_|"); rewrite -mulrBl normrM => eq.
case=> [ge0_r lt_rd] [ge0_r' lr_r'd]; have: `|r - r'| < `|d|.
  rewrite ltr_norml ltr_paddl // 1:ltr_oppr 1:opprK //=.
  by rewrite ltr_naddr // oppr_le0.
rewrite eq gtr_pmull 1:normr_gt0 // (@ltzS _ 0) normr_le0 subr_eq0.
by move=> ->> /=; move: eq; rewrite subrr normr0P subr_eq0.
qed.

(* -------------------------------------------------------------------- *)
lemma nosmt euclideUl d q r m :
     q * d + r = (m %/ d) * d + (m %% d)
  => 0 <= r < `|d|
  => q = m %/ d /\ r = m %% d.
proof.
case: (d = 0) => [->|]; first by rewrite ler_lt_asym.
move=> nz_d eq le_rd; apply/(@euclideU d)=> //.
by case: (edivzP m d)=> _ /(_ nz_d).
qed.

(* -------------------------------------------------------------------- *)
lemma nosmt modz_ge0 m d : d <> 0 => 0 <= m %% d.
proof.
case: (d = 0) => [->//|nz_d /=].
by case: (edivzP m d)=> _ /(_ nz_d) [].
qed.

(* -------------------------------------------------------------------- *)
lemma nosmt modn_ge0 m d : 0 <= m => 0 <= m %% d.
proof.
move=> ge0_m; case: (d = 0) => [->//|nz_d /=].
+ by rewrite (modz0 m). + by rewrite modz_ge0.
qed.

(* -------------------------------------------------------------------- *)
lemma nosmt ltz_mod m d : d <> 0 => m %% d < `|d|.
proof. by move=> gt0_d; case: (edivzP m d) => _ /(_ _) //; rewrite gtr_eqF. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt ltz_pmod m d : 0 < d => m %% d < d.
proof. by move=> ^h /ltr0_neq0 /ltz_mod/(_ m); rewrite gtr0_norm. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt div0z d: 0 %/ d = 0.
proof.
case: (d = 0) => [->|nz_d]; first by rewrite divz0.
have /= := euclideUl d 0 0 0; rewrite normr_gt0 nz_d /=.
by have [h _] := (edivzP 0 d); move/(_ h); case=> /eq_sym.
qed.

(* -------------------------------------------------------------------- *)
lemma nosmt mod0z d: 0 %% d = 0.
proof. by case: (edivzP 0 d); rewrite div0z /= eq_sym. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt divz_eq (m d : int): m = (m %/ d) * d + (m %% d).
proof. by case: (edivzP m d). qed.

(* -------------------------------------------------------------------- *)
lemma nosmt modzN (m d : int): m %% (-d) = m %% d.
proof.
case: (d = 0) => [->|nz_d]; first by rewrite oppr0.
have [+ _] := edivzP m (-d); have [+ _] := edivzP m d.
move=> {1}->; rewrite mulrN -mulNr => /eq_sym eq.
have := euclideUl d (- (m %/ -d)) (m %% -d) m.
rewrite modz_ge0 1:oppr_eq0 //= -normrN ltz_mod 1:oppr_eq0 //=.
by move/(_ eq) => [].
qed.

(* -------------------------------------------------------------------- *)
lemma nosmt divzN m d : m %/ - d = - (m %/ d).
proof.
case: (d = 0) => [->|nz_d]; first by rewrite 2!(divz0, oppr0).
have := (divz_eq m (-d)); rewrite {1}(divz_eq m d) modzN mulrN.
by rewrite -mulNr => /addIr /(mulIf _ nz_d) ->; rewrite opprK.
qed.

(* -------------------------------------------------------------------- *)
lemma nosmt modz_abs (m d : int): m %% `|d| = m %% d.
proof.
by case: (d < 0) => [/ltr0_norm|/lerNgt /ger0_norm] ->; rewrite ?modzN.
qed.

(* -------------------------------------------------------------------- *)
lemma nosmt edivz_eq d q r:
  0 <= r < `|d| => (q * d + r) %/ d = q.
proof.
move=> lt_rd; have [+ _] := (edivzP (q * d + r) d).
by move/euclideUl/(_ lt_rd)=> [<-].
qed.

(* -------------------------------------------------------------------- *)
lemma nosmt emodz_eq d q r: 0 <= r < `|d| => (q * d + r) %% d = r.
proof.
move=> lt_rd; have [+ _] := (edivzP (q * d + r) d).
by move/euclideUl/(_ lt_rd)=> [_ <-].
qed.

(* -------------------------------------------------------------------- *)
lemma nosmt divz_small m d: 0 <= m < `|d| => m %/ d = 0.
proof. by move=> /edivz_eq /(_ 0). qed.

lemma nosmt modz_small m d: 0 <= m < `|d| => m %% d = m.
proof. by move=> /emodz_eq /(_ 0). qed.

lemma nosmt pmod_small n d: 0 <= n < d => n %% d = n.
proof. by move=> h; apply/modz_small => /#. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt divz_eq0 m d : 0 < d => (0 <= m < d) <=> (m %/ d = 0).
proof. move=> gt0_d; split=> [[ge0_m lt_md]|].
  by rewrite divz_small ?ge0_m //= ltr_normr lt_md.
move=> eq0; rewrite (divz_eq m d) eq0 /=.
by rewrite modz_ge0 ?ltz_pmod ?gtr_eqF.
qed.

(* -------------------------------------------------------------------- *)
lemma nosmt mod2_b2i b : b2i b %% 2 = b2i b.
proof. by rewrite modz_small //; case: b. qed.

lemma nosmt b2i_mod2 i : b2i (i %% 2 <> 0) = i %% 2.
proof.
case: (i %% 2 = 0) => [->//|nz_iM2]; rewrite b2i1.
have: 0 <= i %% 2 < 2 by rewrite modz_ge0 // ltz_pmod.
by rewrite ler_eqVlt eq_sym nz_iM2 /= (@ltzS _ 1) ltzE -eqr_le.
qed.

(* -------------------------------------------------------------------- *)
lemma nosmt oddP z: odd z <=> (z %% 2 <> 0).
proof.
rewrite {1}(divz_eq _ 2); case: (z %% 2 = 0) => /=.
+ by move=> ->/=; rewrite oddM odd2.
move=> nz_z2; suff ->/=: z %% 2 = 1.
+ by rewrite oddD oddM odd2 odd1.
by (have := ltz_pmod z 2 _; last have := modz_ge0 z 2 _) => // /#.
qed.

lemma nosmt oddPn z: !odd z <=> (z %% 2 = 0).
proof. by rewrite oddP /#. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt modz_mod m d : m %% d %% d = m %% d.
proof.
case: (d = 0) => [->|nz_d]; first by rewrite modz0.
rewrite -!(modz_abs _ d) modz_small // normr_id ltz_pmod.
  by rewrite normr_gt0. by rewrite modz_ge0 // normr0P.
qed.

(* -------------------------------------------------------------------- *)
lemma nosmt modzE m d : m %% d = m - (m %/ d) * d.
proof. by have [+ _] - {2}-> := edivzP m d; rewrite addrAC addrN. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt divzE m d : m %/ d * d = m - m %% d.
proof. by rewrite modzE; ring. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt divzMDl q m d : d <> 0 => (q * d + m) %/ d = q + (m %/ d).
proof.
move=> nz_d; have [+ /(_ nz_d) lt_md] - {1}-> := edivzP m d.
by rewrite addrA -mulrDl edivz_eq.
qed.

(* -------------------------------------------------------------------- *)
lemma nosmt divzMDr q m d : d <> 0 => (m + q * d) %/ d = q + (m %/ d).
proof. by move=> nz_d; rewrite (@addrC m); apply/divzMDl. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt modzMDl p m d : (p * d + m) %% d = m %% d.
proof.
case: (d = 0) => [->|nz_d]; first by rewrite mulr0 add0r.
by rewrite modzE divzMDl // mulrDl opprD addrACA addrN -modzE.
qed.

(* -------------------------------------------------------------------- *)
lemma nosmt modzMDr p m d : (m + p * d) %% d = m %% d.
proof. by rewrite addrC modzMDl. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt mulzK m d : d <> 0 => m * d %/ d = m.
proof. by move=> d_nz; rewrite -(addr0 (m*d)) divzMDl // div0z addr0. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt mulKz m d : d <> 0 => d * m %/ d = m.
proof. by move=> d_nz; rewrite mulrC mulzK. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt modz1 x : x %% 1 = 0.
proof. by have /= := ltz_pmod x 1; rewrite (@ltzS _ 0) leqn0 1:modz_ge0. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt divz1 x : x %/ 1 = x.
proof. by rewrite -{1}(mulr1 x) mulzK. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt divzz d : (d %/ d) = b2i (d <> 0).
proof.
case: (d = 0) => [->|nz_d]; first by rewrite divz0.
by rewrite -{1}(mulr1 d) mulKz.
qed.

(* -------------------------------------------------------------------- *)
lemma nosmt divzMpl p m d : 0 < p => p * m %/ (p * d) = m %/ d.
proof.
move: d; have wl: forall d, 0 < d => 0 < p => p * m %/ (p * d) = m %/ d.
  move=> d gt0_d gt0_p; rewrite {1}(divz_eq m d) mulrDr mulrCA.
  rewrite divzMDl ?mulf_neq0 1,2:gtr_eqF // addrC divz_small ?add0r //.
  rewrite pmulr_rge0 ?modz_ge0 //= 1:gtr_eqF //= normrM gtr0_norm //.
  by rewrite ltr_pmul2l // ltz_mod gtr_eqF.
move=> d; case: (d = 0) => [->|]; first by rewrite /= !divz0.
rewrite eqr_le andaE negb_and -!ltrNge => -[/wl //|lt0_d gt0_p].
by rewrite -(opprK d) mulrN divzN wl 1:oppr_gt0 // -divzN.
qed.

(* -------------------------------------------------------------------- *)
lemma nosmt divzMpr p m d : 0 < p => m * p %/ (d * p) = m %/ d.
proof. by move=> p_gt0; rewrite -!(mulrC p) divzMpl. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt modzDl m d : (d + m) %% d = m %% d.
proof. by rewrite -{1}(@mul1r d) modzMDl. qed.

lemma nosmt modzDr m d : (m + d) %% d = m %% d.
proof. by rewrite addrC modzDl. qed.

lemma nosmt modzz d : d %% d = 0.
proof. by rewrite -{1}(@addr0 d) modzDl mod0z. qed.

lemma nosmt modzMl p d : (p * d) %% d = 0.
proof. by rewrite -(@addr0 (p*d)) modzMDl mod0z. qed.

lemma nosmt modzMr p d : (d * p) %% d = 0.
proof. by rewrite mulrC modzMl. qed.

lemma nosmt modzDml m n d : (m %% d + n) %% d = (m + n) %% d.
proof. by rewrite {2}(divz_eq m d) -addrA modzMDl. qed.

lemma nosmt modzDmr m n d : (m + n %% d) %% d = (m + n) %% d.
proof. by rewrite !(addrC m) modzDml. qed.

lemma nosmt modzDm m n d : (m %% d + n %% d) %% d = (m + n) %% d.
proof. by rewrite modzDml modzDmr. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt modzMml m n d : ((m %% d) * n) %% d = (m * n) %% d.
proof. by rewrite {2}(divz_eq m d) mulrDl mulrAC modzMDl. qed.

lemma nosmt modzMmr m n d : (m * (n %% d)) %% d = (m * n) %% d.
proof. by rewrite !(mulrC m) modzMml. qed.

lemma nosmt modzMm m n d : ((m %% d) * (n %% d)) %% d = (m * n) %% d.
proof. by rewrite modzMml modzMmr. qed.

lemma nosmt modzNm m d : (- (m %% d)) %% d = (- m) %% d.
proof. by rewrite -mulN1r modzMmr mulN1r. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt mulz_modr p m d : 0 < p => p * (m %% d) = (p * m) %% (p * d).
proof. by move=> p_gt0; rewrite !modzE mulrBr divzMpl // mulrCA. qed.

lemma nosmt mulz_modl p m d : 0 < p => (m %% d) * p = (m * p) %% (d * p).
proof. by rewrite -!(mulrC p); apply/mulz_modr. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt dvdzE d m : d %| m <=> (m %% d = 0).
proof. by []. qed.

lemma nosmt dvdz0 d : d %| 0.
proof. by rewrite dvdzE mod0z. qed.

lemma nosmt dvd0z m : 0 %| m <=> m = 0.
proof. by rewrite dvdzE modz0. qed.

lemma nosmt dvd1z m : 1 %| m.
proof. by rewrite dvdzE modz1. qed.

lemma nosmt dvdz1 d : d %| 1 <=> `|d| = 1.
proof.                        (* FIXME: test-case for case analysis *)
move: d; have wlog: forall d, 0 <= d => d %| 1 <=> `|d| = 1; first last.
  move=> d; case: (0 <= d) => [/wlog//|/ltrNge/ltrW le0_d].
  by rewrite -{1}(opprK d) dvdzE modzN /= -dvdzE wlog ?normrN // oppr_ge0.
move=> d; case: (1 < d) => [lt1_d ge0_d|/lerNgt].
  have lt1_nd: 1 < `|d| by apply/(ltr_le_trans d)/ler_norm.
  by rewrite dvdzE modz_small /= ?gtr_eqF.
rewrite ler_eqVlt=> -[->|]; first by rewrite dvd1z.
rewrite (@ltzS _ 0) => le0d ge0d; have ->: d = 0.
  by rewrite eqr_le le0d ge0d.
by rewrite normr0 /= dvdzE modz0.
qed.

lemma nosmt dvdzz m : m %| m.
proof. by rewrite dvdzE modzz. qed.

lemma nosmt dvdzP d m : (d %| m) <=> (exists q, m = q * d).
proof.
rewrite dvdzE; split=> [|[q->]]; last by rewrite modzMl.
by move=> eq; exists (m %/ d); rewrite {1}(divz_eq m d) eq.
qed.

lemma nosmt dvdz_mull d m n : d %| n => d %| m * n.
proof. by move/dvdzP=> [q ->]; rewrite dvdzE mulrA modzMl. qed.

lemma nosmt dvdz_mulr d m n : d %| m => d %| m * n.
proof. by move=> d_m; rewrite mulrC dvdz_mull. qed.

lemma nosmt dvdz_mul d1 d2 m1 m2 :
  d1 %| m1 => d2 %| m2 => d1 * d2 %| m1 * m2.
proof.
move=> /dvdzP[q1 ->] /dvdzP[q2 ->].
by rewrite mulrCA -mulrA 2?dvdz_mull // dvdzz.
qed.

lemma nosmt dvdz_trans n d m : d %| n => n %| m => d %| m.
proof. by move=> dv_dn /dvdzP[q ->]; apply/dvdz_mull. qed.

lemma nosmt dvdz_le m n : n <> 0 => m %| n => `|m| <= `|n|.
proof.
move=> nz_n /dvdzP [q ^nE ->]; rewrite normrM.
case: (m = 0) => [->//|nz_m]; rewrite ler_pmull 1:normr_gt0 //.
have := normr_ge0 q; rewrite ler_eqVlt => -[|].
+ by rewrite eq_sym normr0P => ->>; move: nE nz_n.
+ by rewrite ltzE.
qed.

(* -------------------------------------------------------------------- *)
lemma nosmt dvdzD d m1 m2 : d %| m1 => d %| m2 => d %| (m1 + m2).
proof.
by move=> /dvdzP[q1 ->] /dvdzP[q2 ->]; rewrite -mulrDl &(dvdz_mull) dvdzz.
qed.

lemma nosmt dvdzN d m : d %| m => d %| -m.
proof. by move/dvdzP=> [q ->]; rewrite -mulNr &(dvdz_mull) dvdzz. qed.

lemma nosmt dvdzB d m1 m2 : d %| m1 => d %| m2 => d %| (m1 - m2).
proof. by move=> h1 h2; apply/dvdzD/dvdzN. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt dvdz_eq d m : (d %| m) <=> (m %/ d * d = m).
proof. by rewrite dvdzE modzE subr_eq0 eq_sym. qed.

lemma nosmt dvdz_exp2l p m n : 0 <= m <= n => (p ^ m %| p ^ n).
proof.
move=> [ge0_m le_mn]; rewrite dvdzE; rewrite -(subrK n m).
by rewrite exprDn ?subr_ge0 // modzMl.
qed.

(* -------------------------------------------------------------------- *)
lemma nosmt dvdz_modzDl (m n d : int) : d %| m => (m + n) %% d = n %% d.
proof. by rewrite -modzDml=> /dvdzE ->. qed.

lemma nosmt dvdz_modzDr (m n d : int) : d %| n => (m + n) %% d = m %% d.
proof. by rewrite -modzDmr=> /dvdzE ->. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt modz_dvd m p q: q %| p => (m %% p) %% q = m %% q.
proof.
move=> dv_qp; rewrite (modzE _ p) -mulNr.
by move/dvdz_eq: dv_qp=> {2}<-; rewrite mulrA modzMDr.
qed.

(* -------------------------------------------------------------------- *)
lemma nosmt divNz (m d : int) :
  0 < m => 0 < d => (-m) %/ d = - ((m-1) %/ d + 1).
proof.
move=> gt0_m gt0_d; rewrite !edivz_def.
rewrite oppr_ge0 lerNgt gt0_m -ltzS -addrA gt0_m /=.
rewrite opprD opprK; case _: (edivn _ _) => q r E /=.
by rewrite mulrN signz_gt0.
qed.

lemma nosmt modNz m d : 0 < m => 0 < d =>
  (-m) %% d = d - 1 - (m-1) %% d.
proof. by move=> gt0_m gt0_d; rewrite !modzE !divNz //; ring. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt divzK d m : d %| m => m %/ d * d = m.
proof. by move/dvdz_eq. qed.

lemma nosmt lez_floor m d : d <> 0 => m %/ d * d <= m.
proof. by rewrite -subr_ge0 -modzE; apply/modz_ge0. qed.

lemma nosmt ltz_ceil m d : 0 < d => m < (m %/ d + 1) * d.
proof.
by move=> d_gt0; rewrite mulrDl mul1r -ltr_subl_addl -modzE ltz_pmod.
qed.

lemma nosmt ltz_divLR m n d : 0 < d => (m %/ d < n) <=> (m < n * d).
proof.
move=> d_gt0; split.
  rewrite -lez_add1r addrC -(ler_pmul2r _ d_gt0).
  by apply/ltr_le_trans/ltz_ceil.
rewrite -(ltr_pmul2r _ d_gt0 _ n) //; apply/ler_lt_trans.
by apply/lez_floor; rewrite gtr_eqF.
qed.

lemma nosmt lez_divRL m n d : 0 < d =>
  (m <= n %/ d) <=> (m * d <= n).
proof. by move=> d_gt0; rewrite !lerNgt ltz_divLR. qed.

lemma nosmt lez_divLR d m n : 0 < d => d %| m =>
  (m %/ d <= n) <=> (m <= n * d).
proof. by move=> /ler_pmul2r <- /divzK->. qed.

lemma nosmt ltz_divRL d m n : 0 < d => d %| m =>
  (n < m %/ d) <=> (n * d < m).
proof. by move=> /ltr_pmul2r <- /divzK->. qed.

lemma nosmt eqz_div d m n : d <> 0 => d %| m =>
  (n = m %/ d) <=> (n * d = m).
proof. by move=> /mulIf/inj_eq <- /divzK /= ->. qed.

lemma nosmt eqz_mul d m n : d <> 0 => d %| m =>
  (m = n * d) <=> (m %/ d = n).
proof. by move=> d_gt0 dv_d_m; rewrite eq_sym -eqz_div // eq_sym. qed.

lemma nosmt leq_div2r (d m n : int) :
  m <= n => 0 <= d => m %/ d <= n %/ d.
proof.
move=> le_mn /ler_eqVlt [<-|gt0_d]; first by rewrite !divz0.
by rewrite lez_divRL // (ler_trans m) -?leq_divRL // lez_floor gtr_eqF.
qed.

lemma nosmt divz_ge0 m d : 0 < d => (0 <= m %/ d) <=> (0 <= m).
proof.
move=> gt0_d; case: (0 <= m)=> /= [ge0_m|].
  by rewrite lez_divRL. by rewrite -!ltrNge ltz_divLR.
qed.

lemma nosmt leq_trunc_div m d : 0 <= m => 0 <= d => m %/ d * d <= m.
proof.
move=> ge0_m ge0_d; rewrite {2}(divz_eq m d).
by rewrite ler_paddr // modn_ge0.
qed.

lemma nosmt leq_div m d : 0 <= m => 0 <= d => m %/ d <= m.
proof.
move=> ge0_m; rewrite ler_eqVlt => -[<-|]; 1: by rewrite divz0.
move=> gt0_d; rewrite -(ler_pmul2r d) //.
apply/(ler_trans m); first by apply/leq_trunc_div/ltrW.
by apply/ler_pemulr => //; rewrite -(ltzE 0).
qed.

lemma nosmt lez_div m d : `|m %/ d| <= `|m|.
proof.
move: d; have wlog: forall d, 0 < d => `|m %/ d| <= `|m|; last first.
  move=> d; case: (0 < d) => [/wlog//|/lerNgt /ler_eqVlt [->|]].
    by rewrite divz0 normr0 normr_ge0.
  by move=> lt0_d; rewrite -(opprK d) divzN normrN wlog oppr_gt0.
move=> d gt0_d; case: (0 <= m) => [ge0_m|].
  by rewrite !ger0_norm ?divz_ge0 // ?leq_div // ltrW.
rewrite lerNgt /= => lt0_m; rewrite !ler0_norm 1,2:ltrW //.
  by rewrite ltrNge divz_ge0 // lerNgt.
rewrite -{1}(opprK m) divNz ?oppr_gt0 // opprK.
rewrite -ltzE; apply/(ler_lt_trans (-(m+1))).
  rewrite opprD; apply/leq_div/ltrW=> //.
  by rewrite subr_ge0 -(ltzE 0) oppr_gt0.
by rewrite ltzE opprD -addrA.
qed.

(* -------------------------------------------------------------------- *)
lemma nosmt divzDl m n d : d %| m => (m + n) %/ d = (m %/ d) + (n %/ d).
proof.
case: (d = 0) => [->|nz_d]; first by rewrite !divz0.
by move/divzK=> {1}<-; rewrite divzMDl.
qed.

lemma nosmt divzDr m n d : d %| n => (m + n) %/ d = (m %/ d) + (n %/ d).
proof. by move=> dv_n; rewrite addrC divzDl // addrC. qed.

(* ==================================================================== *)
op gcd_spec a b = fun z =>
     (0 <= z /\ z %| a /\ z %| b)
  /\ (forall x, x %| a => x %| b => x <= z).

lemma gcd_spec a b : (a, b) <> (0, 0) => exists z, gcd_spec a b z.
proof.
wlog: a b / (`|a| <= `|b|) => [wlog|le_ab nz_ab].
+ case: (leVge `|a| `|b|) => [|le_ba nz_ab]; first by apply: wlog.
  case: (wlog _ _ le_ba _) => [|z [[# 3? h]]].
  + by apply: contra nz_ab.
  + by exists z; do! split => //; move=> *; apply: h.
case: (a = 0) => [->>|]; 1: (exists `|b|; do! split=> //).
+ by rewrite dvdz0.
+ by rewrite {2}signzE dvdz_mull dvdzz.
+ by move=> x _ xDb; rewrite (ler_trans `|x|) 1:ler_norm dvdz_le.
move=> nz_a; have nz_b : b <> 0.
+ by apply: contraL le_ab => ->; rewrite normr0 lerNgt /= normr_gt0.
pose E := fun z => (`|a * b| - z) %| a /\ (`|a * b| - z %| b).
have ge0_pE: 0 <= `|a * b| - 1.
+ have := normr_ge0 (a * b); rewrite subr_ge0 ler_eqVlt.
  rewrite ltzE /= => -[] //; rewrite eq_sym.
  by rewrite normrM mulf_eq0 !normr0P !(nz_a, nz_b).
have pE: E (`|a * b| - 1); first move=> @/pcap @/E /=; do! split.
+ by rewrite opprB addrCA subrr /= dvd1z.
+ by rewrite opprB addrCA subrr /= dvd1z.
have nzE: !sempty (pcap E); 1: by apply/semptyNP; exists (`|a * b| - 1).
pose d := `|a * b| - pmin E; have [da db]: d %| a /\ d %| b.
+ by case: (pmin_mem _ nzE).
exists d; do! split => //.
+ rewrite /d subr_ge0 &(ler_trans (pmin E + 1)) 1:ler_addl //.
  by have := pmin_min _ _ nzE ge0_pE pE; rewrite ler_subr_addl addrC.
move=> x xDa xDb @/d; rewrite ler_subr_addl addrC -ler_subr_addl.
apply: pmin_min; first exact nzE.
+ rewrite subr_ge0 (ler_trans _ _ _ (ler_norm _)).
  by rewrite dvdz_le 1:mulf_neq0 // dvdz_mull.
+ by rewrite /E !opprB !(addrCA _ x) subrr.
qed.

op gcd a b = if (a, b) = (0, 0) then 0 else choiceb (gcd_spec a b) 0.

lemma nosmt gcdP a b : (a, b) <> (0, 0) =>
     0 <= gcd a b
  /\ gcd a b %| a
  /\ gcd a b %| b
  /\ (forall z, z %| a => z %| b => z <= gcd a b).
proof.
by move=> ^nz_ab /gcd_spec/choicebP/(_ 0) /= []; rewrite /gcd nz_ab.
qed.

lemma ge0_gcd a b : 0 <= gcd a b.
proof. by case: ((a, b) = (0, 0)) => [@/gcd ->//|/gcdP]. qed.

hint exact : ge0_gcd.

lemma dvdz_gcdr a b : gcd a b %| b.
proof. 
case: (b = 0) => [->|nz_b]; 1: by apply: dvdz0.
by have /gcdP: (a, b) <> (0, 0) by apply: contra nz_b.
qed.

lemma dvdz_gcdl a b : gcd a b %| a.
proof. 
case: (a = 0) => [->|nz_a]; 1: by apply: dvdz0.
by have /gcdP: (a, b) <> (0, 0) by apply: contra nz_a.
qed.

hint exact : dvdz_gcdl dvdz_gcdr.

lemma gcd_max a b z : (a, b) <> (0, 0) =>
  z %| a => z %| b => z <= gcd a b.
proof. by case/gcdP => _ [# 2?]; apply. qed.

lemma gcd_eq0 a b : gcd a b = 0 <=> ((a, b) = (0, 0)).
proof.
split=> [|[-> ->]] //= z_gcd; rewrite -(dvd0z a) -(dvd0z b).
by rewrite -z_gcd !(dvdz_gcdl, dvdz_gcdr).
qed.

lemma nosmt gcd_uniq a b z : (a, b) <> (0, 0) =>
     0 <= z => z %| a => z %| b
  => (forall x, x %| a => x %| b => x <= z)
  => z = gcd a b.
proof.
move=> nz_ab + za zb hmax; rewrite ler_eqVlt => -[<<-|gt0_z].
+ by move: za zb; rewrite !dvd0z => -> ->.
by rewrite eqr_le hmax /= 1,2:(dvdz_gcdl, dvdz_gcdr) gcd_max.
qed.

lemma gcdC a b : gcd a b = gcd b a.
proof.
case: ((a, b) = (0, 0)) => [[-> -> //]|nz_ab].
apply: gcd_uniq => //; first by apply: contra nz_ab.
by move=> z xb xa; apply: gcd_max.
qed.

lemma gcd00 : gcd 0 0 = 0.
proof. by []. qed.

hint simplify gcd00.

lemma gcd0z a : gcd 0 a = `|a|.
proof.
case: (a = 0) => [->//=|nz_a].
apply/eq_sym/gcd_uniq => //=; first by rewrite normr_ge0.
+ by rewrite dvdz0.
+ by rewrite {2}signzE dvdz_mull dvdzz.
+ by move=> x _ xDa; rewrite &(ler_trans `|x|) 1:ler_norm dvdz_le.
qed.

lemma gcdz0 a : gcd a 0 = `|a|.
proof. by rewrite gcdC gcd0z. qed.

hint simplify gcd0z, gcdz0.

lemma gcd1z a : gcd 1 a = 1.
proof.
apply/eq_sym/gcd_uniq => //.
+ by rewrite dvdzz. + by rewrite dvd1z.
+ by move=> x; rewrite dvdz1 => <- _; rewrite ler_norm.
qed.

lemma gcdz1 a : gcd a 1 = 1.
proof. by rewrite gcdC gcd1z. qed.

hint simplify gcd1z, gcdz1.

lemma gcdNz a b : gcd (- a)%Int b = gcd a b.
proof.
case: ((a, b) = (0, 0)) => [[-> ->] //|nz_ab]; apply: gcd_uniq => //.
+ by rewrite -{2}(opprK a) &(dvdzN) dvdz_gcdl.
+ move=> x xDa xDb; rewrite &(gcd_max) // 2:&(dvdzN) //.
  by apply: contra nz_ab => /=; rewrite oppr_eq0.
qed.

lemma gcdzN a b : gcd a (- b)%Int = gcd a b.
proof. by rewrite gcdC gcdNz gcdC. qed.

hint simplify gcdNz, gcdzN.

lemma gcd_modr a b : gcd a (b %% a) = gcd a b.
proof.
case: ((a, b) = (0, 0)) => [[-> ->]|nz_ab]; 1: by rewrite modz0.
apply: gcd_uniq=> //.
+ by have := dvdz_gcdr a (b %% a); rewrite !dvdzE modz_dvd 1:dvdz_gcdl.
+ move=> x xa xb; apply: gcd_max => //.
  * by apply: contra nz_ab => /= -[->]; rewrite modz0.
  by rewrite dvdzE modz_dvd.
qed.

lemma gcd_modl a b : gcd (a %% b) b = gcd a b.
proof. by rewrite gcdC gcd_modr gcdC. qed.

lemma gcdMDl q a b : gcd a (q * a + b)%Int = gcd a b.
proof. by rewrite -gcd_modr modzMDl gcd_modr. qed.

lemma gcdDl a b : gcd a (a + b)%Int = gcd a b.
proof. by rewrite -{2}(mul1r a) gcdMDl. qed.

lemma gcdDr a b : gcd a (b + a)%Int = gcd a b.
proof. by rewrite addrC gcdDl. qed.

lemma gcdMl b a : gcd b (a * b)%Int = `|b|.
proof. by rewrite -(addr0 (a * b)) gcdMDl gcdz0. qed.

lemma gcdMr b a : gcd b (b * a)%Int = `|b|.
proof. by rewrite mulrC gcdMl. qed.

lemma nosmt Bachet_Bezout (a b : int) :
  exists u v, u * a + v * b = gcd a b.
proof.
case: (a = 0) => [->/=|nz_a].
+ by exists (signz b); rewrite signVzE.
pose E d := 0 < d /\ exists u v, d = u * a + v * b.
have nzE: !sempty (pcap E).
+ apply/semptyNP; exists `|a| => @/E @/pcap /=.
 rewrite normr_ge0 normr_gt0 nz_a /=.
  by exists (signz a) 0 => /=; apply: signVzE.
case: (pmin_mem _ nzE); (pose d0 := pmin E) => gt0_d [a0 b0] d0E.
exists a0 b0; apply: gcd_uniq; rewrite ?nz_a // -?d0E.
+ by apply/negP => -[]; rewrite nz_a.
+ by rewrite ltrW.
+ rewrite dvdzE eqr_le modz_ge0 1:gtr_eqF //= lerNgt; apply/negP.
  move=> gt0_ad0; have: E (a %% d0); 1: move=> @/E.
  * rewrite gt0_ad0 /=; rewrite modzE {2}d0E.
    rewrite mulrDr opprD addrA !mulrA -{1}(mul1r a) -mulrBl.
    move: (1 - _)%Int => u; move: (_ %/ _ * _)%Int => v.
    by exists u (-v); rewrite mulNr.
  move=> Ead0; have := pmin_min _ _ nzE _ Ead0.
  * by rewrite ltrW. * by rewrite lerNgt /= ltz_pmod.
+ rewrite dvdzE eqr_le modz_ge0 1:gtr_eqF //= lerNgt; apply/negP.
  move=> gt0_bd0; have: E (b %% d0); 1: move=> @/E.
  * rewrite gt0_bd0 /=; rewrite modzE {2}d0E.
    rewrite mulrDr opprD !addrA !mulrA -addrAC -{1}(mul1r b) -mulrBl.
    move: (1 - _)%Int => u; move: (_ %/ _ * _)%Int => v.
    by exists (-v) u; rewrite mulNr addrC.
  move=> Ebd0; have := pmin_min _ _ nzE _ Ebd0.
  * by rewrite ltrW. * by rewrite lerNgt /= ltz_pmod.
+ move=>z za zb; rewrite &(ler_trans `|z|) 1:ler_norm.
  rewrite -(gtr0_norm d0) // dvdz_le 1:gtr_eqF //.
  by rewrite d0E &(dvdzD) dvdz_mull.
qed.

(* ==================================================================== *)
op coprime a b = gcd a b = 1.

lemma Bezout (a b : int) : coprime a b =>
  exists u v, u * a + v * b = 1.
proof. by move=> @/coprime <-; apply: Bachet_Bezout. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt modinv p a : coprime p a => exists b, p %| (a * b - 1)%Int.
proof.
case/Bezout => u v; rewrite eq_sym (mulrC v a) addrC -subr_eq => h.
by exists v; rewrite -h addrAC /= &(dvdzN) dvdz_mull dvdzz.
qed.

(* -------------------------------------------------------------------- *)
op invm a p = choiceb (fun b => a * b %% p = 1) a.

lemma invmP p a : 1 < p => coprime p a => (a * invm a p) %% p = 1.
proof.
move=> gt1_p; case/modinv=> b /dvdzP[q]; rewrite subr_eq (addrC _ 1)=> h.
rewrite /invm; apply/(choicebP (fun b=> a * b %% p = 1)).
by exists b=> /=; rewrite h modzMDr modz_small // /#.
qed.

(* -------------------------------------------------------------------- *)
op prime a = 1 < a /\ (forall q, q %| a => `|q| = 1 \/ `|q| = a).

lemma gt1_prime p : prime p => 1 < p.
proof. by case. qed.

lemma gt0_prime p : prime p => 0 < p.
proof. by move/gt1_prime/(ltr_trans _ _ _ ltr01). qed.

lemma nosmt prime_coprime p : prime p =>
  forall a, a %% p <> 0 => coprime p a.
proof.
move=> pm_p a nz_a; have h := dvdz_gcdl p a.
case: pm_p => gt1_p /(_ _ h) => {h}; rewrite ger0_norm ?ge0_gcd.
case=> // /eq_sym pE; have: p %| a  by rewrite {1}pE dvdz_gcdr.
by rewrite dvdzE nz_a.
qed.

(* -------------------------------------------------------------------- *)
lemma nosmt modinv_prime p : prime p =>
  forall a, a %% p <> 0 => exists b, (a * b) %% p = 1.
proof.
move=> pm_p a nz_a; have: coprime p (a %% p).
+ have nz_p: p <> 0 by rewrite gtr_eqF // gt0_prime.
  have h := dvdz_gcdl p (a %% p); case: pm_p=> gt1_p.
  move/(_ _ h) => {h}; rewrite ger0_norm ?ge0_gcd.
  case=> // /eq_sym pE; have: p %| (a %% p).
  * by rewrite {1}pE dvdz_gcdr.
  by rewrite dvdzE modz_mod.
case/modinv=> b /dvdzP[q]; rewrite subr_eq (addrC _ 1) -subr_eq.
move/(congr1 (fun x => x %% p)) => /=.
rewrite -mulNr modzMDr modzMml => h; exists b.
by rewrite h modz_small //= ltr_normr gt1_prime.
qed.

lemma mulmV p a : prime p => a %% p <> 0 => (a * invm a p) %% p = 1.
proof.
move=> ^/gt1_prime gt1_p + nz_a - /prime_coprime.
by move=> /(_ a nz_a); apply/invmP.
qed.

(* ==================================================================== *)
(* FIXME: should be supersed by IntDiv                                  *)
lemma nosmt modz_dvd_pow n p i k:
  0 <= n <= p => i %% k^p %% k^n = i %% k^n.
proof. by move=> le_np; apply/modz_dvd/dvdz_exp2l. qed.

lemma nosmt modz_pow_split n p i k : 0 <= p <= n =>
   i = i %/ k^n * k^n + (i %% k^n %/ k^p) * k^p + i %% k^p.
proof.
move=> lt_pn; rewrite {1}(divz_eq i (k^n)); rewrite -addrA; congr.
by rewrite {1}(divz_eq (i %% k^n) (k^p)) modz_dvd_pow.
qed.

lemma nosmt modz_pow2_div n p i: 0 <= i => 0 <= p <= n =>
  (i %% 2^n) %/ 2^p = (i %/ 2^p) %% 2^(n-p).
proof. admitted.
