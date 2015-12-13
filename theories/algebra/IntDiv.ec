(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2015 - IMDEA Software Institute
 * Copyright (c) - 2012--2015 - Inria
 * 
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
require import Fun Int IntExtra Ring StdOrder.
(*---*) import Ring.IntID IntOrder.

(* -------------------------------------------------------------------- *)
op (%/) : int -> int -> int.
op (%%) : int -> int -> int.

axiom nosmt edivzP (m d : int):
  m = (m %/ d) * d + (m %% d) /\ (d <> 0 => 0 <= m %% d < `|d|).

axiom divz0 m: m %/ 0 = 0.

(* -------------------------------------------------------------------- *)
op (%|) (m d : int) = (d %% m = 0).

(* -------------------------------------------------------------------- *)
lemma nosmt euclideU d q q' r r':
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
lemma modz0 m: m %% 0 = m.
proof. by have [/= <-] := edivzP m 0. qed.

(* -------------------------------------------------------------------- *)
lemma modz_ge0 m d : d <> 0 => 0 <= m %% d.
proof.
case: (d = 0) => [->|nz_d /=]; first by rewrite modz0.
by case: (edivzP m d)=> _ /(_ nz_d) [].
qed.

(* -------------------------------------------------------------------- *)
lemma ltz_mod m d : d <> 0 => m %% d < `|d|.
proof. by move=> gt0_d; case: (edivzP m d) => _ /(_ _) //; rewrite gtr_eqF. qed.

(* -------------------------------------------------------------------- *)
lemma ltz_pmod m d : 0 < d => m %% d < d.
proof. by move=> ^h /ltr0_neq0 /ltz_mod/(_ m); rewrite gtr0_norm. qed.

(* -------------------------------------------------------------------- *)
lemma div0z d: 0 %/ d = 0.
proof.
case: (d = 0) => [->|nz_d]; first by rewrite divz0.
have /= := euclideUl d 0 0 0; rewrite normr_gt0 nz_d /=.
by have [h _] := (edivzP 0 d); move/(_ h); case=> /eq_sym.
qed.

(* -------------------------------------------------------------------- *)
lemma mod0z d: 0 %% d = 0.
proof. by case: (edivzP 0 d); rewrite div0z /= eq_sym. qed.

(* -------------------------------------------------------------------- *)
lemma divz_eq (m d : int): m = (m %/ d) * d + (m %% d).
proof. by case: (edivzP m d). qed.

(* -------------------------------------------------------------------- *)
lemma modzN (m d : int): m %% (-d) = m %% d.
proof.
case: (d = 0) => [->|nz_d]; first by rewrite oppr0.
have [+ _] := edivzP m (-d); have [+ _] := edivzP m d.
move=> {1}->; rewrite mulrN -mulNr => /eq_sym eq.
have := euclideUl d (- (m %/ -d)) (m %% -d) m.
rewrite modz_ge0 1:oppr_eq0 //= -normrN ltz_mod 1:oppr_eq0 //=.
by move/(_ eq) => [].
qed.

(* -------------------------------------------------------------------- *)
lemma divzN m d : m %/ - d = - (m %/ d).
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
lemma edivz_eq d q r:
  0 <= r < `|d| => (q * d + r) %/ d = q.
proof.
move=> lt_rd; have [+ _] := (edivzP (q * d + r) d).
by move/euclideUl/(_ lt_rd)=> [<-].
qed.

(* -------------------------------------------------------------------- *)
lemma emodz_eq d q r: 0 <= r < `|d| => (q * d + r) %% d = r.
proof.
move=> lt_rd; have [+ _] := (edivzP (q * d + r) d).
by move/euclideUl/(_ lt_rd)=> [_ <-].
qed.

(* -------------------------------------------------------------------- *)
lemma divz_small m d: 0 <= m < `|d| => m %/ d = 0.
proof. by move=> /edivz_eq /(_ 0). qed.

lemma modz_small m d: 0 <= m < `|d| => m %% d = m.
proof. by move=> /emodz_eq /(_ 0). qed.

(* -------------------------------------------------------------------- *)
lemma divz_eq0 m d : 0 < d => (0 <= m < d) <=> (m %/ d = 0).
proof. move=> gt0_d; split=> [[ge0_m lt_md]|].
  by rewrite divz_small ?ge0_m //= ltr_normr lt_md.
move=> eq0; rewrite (divz_eq m d) eq0 /=.
by rewrite modz_ge0 ?ltz_pmod ?gtr_eqF.
qed.

(* -------------------------------------------------------------------- *)
lemma mod2_b2i b : b2i b %% 2 = b2i b.
proof. by rewrite modz_small //; case: b. qed.

lemma b2i_mod2 i : b2i (i %% 2 <> 0) = i %% 2.
proof.
case: (i %% 2 = 0) => [->//|nz_iM2]; rewrite b2i1.
have: 0 <= i %% 2 < 2 by rewrite modz_ge0 // ltz_pmod.
by rewrite ler_eqVlt eq_sym nz_iM2 /= (@ltzS _ 1) ltzE -eqr_le.
qed.

(* -------------------------------------------------------------------- *)
lemma nosmt modz_mod m d : m %% d %% d = m %% d.
proof.
case: (d = 0) => [->|nz_d]; first by rewrite modz0.
rewrite -!(modz_abs _ d) modz_small // normr_id ltz_pmod.
  by rewrite normr_gt0. by rewrite modz_ge0 // normr0P.
qed.

(* -------------------------------------------------------------------- *)
lemma modzE m d : m %% d = m - (m %/ d) * d.
proof. by have [+ _] - {2}-> := edivzP m d; rewrite addrAC addrN. qed.

(* -------------------------------------------------------------------- *)
lemma divzE m d : m %/ d * d = m - m %% d.
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
lemma mulzK m d : d <> 0 => m * d %/ d = m.
proof. by move=> d_nz; rewrite -(addr0 (m*d)) divzMDl // div0z addr0. qed.

(* -------------------------------------------------------------------- *)
lemma mulKz m d : d <> 0 => d * m %/ d = m.
proof. by move=> d_nz; rewrite mulrC mulzK. qed.

(* -------------------------------------------------------------------- *)
lemma modz1 x : x %% 1 = 0.
proof. by have /= := ltz_pmod x 1; rewrite (@ltzS _ 0) leqn0 1:modz_ge0. qed.

(* -------------------------------------------------------------------- *)
lemma divz1 x : x %/ 1 = x.
proof. by rewrite -{1}(mulr1 x) mulzK. qed.

(* -------------------------------------------------------------------- *)
lemma divzz d : (d %/ d) = b2i (d <> 0).
proof.
case: (d = 0) => [->|nz_d]; first by rewrite divz0.
by rewrite -{1}(mulr1 d) mulKz.
qed.

(* -------------------------------------------------------------------- *)
lemma divzMpl p m d : 0 < p => p * m %/ (p * d) = m %/ d.
proof.
move: d; have wl: forall d, 0 < d => 0 < p => p * m %/ (p * d) = m %/ d.
  move=> d gt0_d gt0_p; rewrite {1}(divz_eq m d) mulrDr mulrCA.
  rewrite divzMDl ?mulf_neq0 1,2:gtr_eqF // addrC divz_small ?add0r //.
  rewrite pmulr_rge0 ?modz_ge0 //= 1:gtr_eqF //= normrM gtr0_norm //.
  by rewrite ltr_pmul2l // ltz_mod gtr_eqF.
move=> d; case: (d = 0) => [->|]; first by rewrite ?divz0.
rewrite eqr_le anda_and -nand -!ltrNge => -[/wl //|lt0_d gt0_p].
by rewrite -(opprK d) mulrN divzN wl 1:oppr_gt0 // -divzN.
qed.

(* -------------------------------------------------------------------- *)
lemma divzMpr p m d : 0 < p => m * p %/ (d * p) = m %/ d.
proof. by move=> p_gt0; rewrite -!(mulrC p) divzMpl. qed.

(* -------------------------------------------------------------------- *)
lemma modzDl m d : (d + m) %% d = m %% d.
proof. by rewrite -{1}(@mul1r d) modzMDl. qed.

lemma modzDr m d : (m + d) %% d = m %% d.
proof. by rewrite addrC modzDl. qed.

lemma modzz d : d %% d = 0.
proof. by rewrite -{1}(@addr0 d) modzDl mod0z. qed.

lemma modzMl p d : (p * d) %% d = 0.
proof. by rewrite -(@addr0 (p*d)) modzMDl mod0z. qed.

lemma modzMr p d : (d * p) %% d = 0.
proof. by rewrite mulrC modzMl. qed.

lemma modzDml m n d : (m %% d + n) %% d = (m + n) %% d.
proof. by rewrite {2}(divz_eq m d) -addrA modzMDl. qed.

lemma modzDmr m n d : (m + n %% d) %% d = (m + n) %% d.
proof. by rewrite !(addrC m) modzDml. qed.

lemma nosmt modzDm m n d : (m %% d + n %% d) %% d = (m + n) %% d.
proof. by rewrite modzDml modzDmr. qed.

(* -------------------------------------------------------------------- *)
lemma modzMml m n d : ((m %% d) * n) %% d = (m * n) %% d.
proof. by rewrite {2}(divz_eq m d) mulrDl mulrAC modzMDl. qed.

lemma modzMmr m n d : (m * (n %% d)) %% d = (m * n) %% d.
proof. by rewrite !(mulrC m) modzMml. qed.

lemma modzMm m n d : ((m %% d) * (n %% d)) %% d = (m * n) %% d.
proof. by rewrite modzMml modzMmr. qed.

lemma modzNm m d : (- (m %% d)) %% d = (- m) %% d.
proof. by rewrite -mulN1r modzMmr mulN1r. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt mulz_modr p m d : 0 < p => p * (m %% d) = (p * m) %% (p * d).
proof. by move=> p_gt0; rewrite !modzE mulrBr divzMpl // mulrCA. qed.

lemma nosmt mulz_modl p m d : 0 < p => (m %% d) * p = (m * p) %% (d * p).
proof. by rewrite -!(mulrC p); apply/mulz_modr. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt dvdzE d m : d %| m <=> (m %% d = 0).
proof. by []. qed.

lemma dvdz0 d : d %| 0.
proof. by rewrite dvdzE mod0z. qed.

lemma dvd0z m : 0 %| m <=> m = 0.
proof. by rewrite dvdzE modz0. qed.

lemma dvd1z m : 1 %| m.
proof. by rewrite dvdzE modz1. qed.

lemma dvdz1 d : d %| 1 <=> `|d| = 1.
proof.                        (* FIXME: test-case for case analysis *)
move: d; have wlog: forall d, 0 <= d => d %| 1 <=> `|d| = 1; first last.
  move=> d; case: (0 <= d) => [/wlog//|/ltrNge/ltrW le0_d].
  by rewrite -{1}(opprK d) dvdzE modzN wlog ?normrN // oppr_ge0.
move=> d; case: (1 < d) => [lt1_d ge0_d|/lerNgt].
  have lt1_nd: 1 < `|d| by apply/(ltr_le_trans d)/ler_norm.
  by rewrite dvdzE modz_small /= ?gtr_eqF.
rewrite ler_eqVlt=> -[->|]; first by rewrite dvd1z.
rewrite (@ltzS _ 0) => le0d ge0d; have ->: d = 0.
  by rewrite eqr_le le0d ge0d.
by rewrite normr0 /= dvdzE modz0.
qed.

lemma dvdzz m : m %| m.
proof. by rewrite dvdzE modzz. qed.

lemma nosmt dvdzP d m : (d %| m) <=> (exists q, m = q * d).
proof.
rewrite dvdzE; split=> [|[q->]]; last by rewrite modzMl.
by move=> eq; exists (m %/ d); rewrite {1}(divz_eq m d) eq.
qed.

lemma dvdz_mull d m n : d %| n => d %| m * n.
proof. by move/dvdzP=> [q ->]; rewrite dvdzE mulrA modzMl. qed.

lemma dvdz_mulr d m n : d %| m => d %| m * n.
proof. by move=> d_m; rewrite mulrC dvdz_mull. qed.

lemma nosmt dvdz_mul d1 d2 m1 m2 :
  d1 %| m1 => d2 %| m2 => d1 * d2 %| m1 * m2.
proof.
move=> /dvdzP[q1 ->] /dvdzP[q2 ->].
by rewrite mulrCA -mulrA 2?dvdz_mull dvdzz.
qed.

lemma nosmt dvdz_trans n d m : d %| n => n %| m => d %| m.
proof. by move=> dv_dn /dvdzP[q ->]; apply/dvdz_mull. qed.

(* -------------------------------------------------------------------- *)
lemma dvdzD d m1 m2 : d %| m1 => d %| m2 => d %| (m1 + m2).
proof.
by move=> /dvdzP[q1 ->] /dvdzP[q2 ->]; rewrite -mulrDl dvdz_mull dvdzz.
qed.

lemma dvdzN d m : d %| m => d %| -m.
proof. by move/dvdzP=> [q ->]; rewrite -mulNr dvdz_mull dvdzz. qed.

lemma dvdzB d m1 m2 : d %| m1 => d %| m2 => d %| (m1 - m2).
proof. by move=> h1 h2; apply/dvdzD/dvdzN. qed.

(* -------------------------------------------------------------------- *)
lemma dvdz_eq d m : (d %| m) <=> (m %/ d * d = m).
proof. by rewrite dvdzE modzE subr_eq0 eq_sym. qed.

lemma dvdz_exp2l p m n : 0 <= m <= n => (p ^ m %| p ^ n).
proof.
move=> [ge0_m le_mn]; rewrite dvdzE; rewrite -(subrK n m).
by rewrite -pow_add // ?subr_ge0 // modzMl.
qed.

(* -------------------------------------------------------------------- *)
lemma dvdz_modzDl (m n d : int) : d %| m => (m + n) %% d = n %% d.
proof. by rewrite -modzDml=> /dvdzE ->. qed.

lemma dvdz_modzDr (m n d : int) : d %| n => (m + n) %% d = m %% d.
proof. by rewrite -modzDmr=> /dvdzE ->. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt modz_dvd m p q: q %| p => (m %% p) %% q = m %% q.
proof.
move=> dv_qp; rewrite (modzE _ p) -mulNr.
by move/dvdz_eq: dv_qp=> {2}<-; rewrite mulrA modzMDr.
qed.

(* -------------------------------------------------------------------- *)
lemma divNz (m d : int) :
  0 < m => 0 < d => (-m) %/ d = - ((m-1) %/ d + 1).
proof. admit. qed.

lemma modNz m d : 0 < m => 0 < d =>
  (-m) %% d = d - 1 - (m - 1) %% d.
proof. by move=> gt0_m gt0_d; rewrite !modzE !divNz //; ring. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt divzK d m : d %| m => m %/ d * d = m.
proof. by move/dvdz_eq. qed.

lemma lez_floor m d : d <> 0 => m %/ d * d <= m.
proof. by rewrite -subr_ge0 -modzE; apply/modz_ge0. qed.

lemma ltz_ceil m d : 0 < d => m < (m %/ d + 1) * d.
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

lemma nosmt lez_divRL m n d : 0 < d => (m <= n %/ d) <=> (m * d <= n).
proof. by move=> d_gt0; rewrite !lerNgt ltz_divLR. qed.

lemma nosmt lez_divLR d m n : 0 < d => d %| m => (m %/ d <= n) <=> (m <= n * d).
proof. by move=> /ler_pmul2r <- /divzK->. qed.

lemma nosmt ltz_divRL d m n : 0 < d => d %| m => (n < m %/ d) <=> (n * d < m).
proof. by move=> /ltr_pmul2r <- /divzK->. qed.

lemma nosmt eqz_div d m n : d <> 0 => d %| m => (n = m %/ d) <=> (n * d = m).
proof. by move=> /mulIf/inj_eq <- /divzK->. qed.

lemma nosmt eqz_mul d m n : d <> 0 => d %| m => (m = n * d) <=> (m %/ d = n).
proof. by move=> d_gt0 dv_d_m; rewrite eq_sym -eqz_div // eq_sym. qed.

(*
lemma nosmt lez_div m d : `|m %/ d| <= `|m|.
proof.
move: d; have wlog: forall d, 0 < d => `|m %/ d| <= `|m|; last first.
  move=> d; case: (0 < d) => [/wlog//|/lerNgt /ler_eqVlt [->|]].
    by rewrite divz0 normr0 normr_ge0.
  by move=> lt0_d; rewrite -(opprK d) divzN normrN wlog oppr_gt0.
admit. qed.
*)
 
lemma nosmt leq_div2r d m n :
  m <= n => 0 <= d => m %/ d <= n %/ d.
proof.
move=> le_mn /ler_eqVlt [<-|gt0_d]; first by rewrite !divz0.
by rewrite lez_divRL // (ler_trans m) -?leq_divRL // lez_floor gtr_eqF.
qed.

lemma divz_ge0 m d : 0 < d => (0 <= m %/ d) <=> (0 <= m).
proof.
move=> gt0_d; case: (0 <= m)=> /= [ge0_m|].
  by rewrite lez_divRL. by rewrite -!ltrNge ltz_divLR.
qed.

(* -------------------------------------------------------------------- *)
lemma divzDl m n d : d %| m => (m + n) %/ d = (m %/ d) + (n %/ d).
proof.
case: (d = 0) => [->|nz_d]; first by rewrite !divz0.
by move/divzK=> {1}<-; rewrite divzMDl.
qed.

lemma divzDr m n d : d %| n => (m + n) %/ d = (m %/ d) + (n %/ d).
proof. by move=> dv_n; rewrite addrC divzDl // addrC. qed.

(* -------------------------------------------------------------------- *)
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
proof. admit. qed.
