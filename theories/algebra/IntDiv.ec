(* -------------------------------------------------------------------- *)
require import Core Int IntMin Ring StdOrder StdBigop List Binomial.
(*---*) import Ring.IntID IntOrder Bigint.

(* -------------------------------------------------------------------- *)
lemma euclide_nat m d : 0 <= m => 0 < d =>
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
lemma edivnP (m d : int): 0 <= m => 0 <= d =>
  euclidef m d (edivn m d).
proof.
move=> ge0_m ge0_d; rewrite edivn_def !ltrNge !(ge0_m, ge0_d) /=.
case: (d = 0) => [->|] //= nz_d; apply/(choicebP (euclidef m d)).
case: (euclide_nat m d _ _) => //; 1: by rewrite ltr_neqAle eq_sym.
by move=> q r [lt_rd mE]; exists (q, r); rewrite /euclidef ger0_norm.
qed.

(* -------------------------------------------------------------------- *)
lemma edivzP_r (m d : int): euclidef m d (edivz m d).
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

lemma edivzP (m d : int) :
  m = (m %/ d) * d + (m %% d) /\ (d <> 0 => 0 <= m %% d < `|d|).
proof. by case: (edivzP_r m d). qed.

(* -------------------------------------------------------------------- *)
lemma divz0 m: m %/ 0 = 0.
proof.
rewrite edivz_def; case: (0 <= m) => /= _.
  by case: (edivn _ _) => q r /=; rewrite signz0.
by case: (edivn _ _) => q r /=; rewrite signz0.
qed.

lemma modz0 m: m %% 0 = m.
proof. by have [/= <-] := edivzP m 0. qed.

(* -------------------------------------------------------------------- *)
lemma euclideU d q q' r r' :
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
lemma euclideUl d q r m :
     q * d + r = (m %/ d) * d + (m %% d)
  => 0 <= r < `|d|
  => q = m %/ d /\ r = m %% d.
proof.
case: (d = 0) => [->|]; first by rewrite ler_lt_asym.
move=> nz_d eq le_rd; apply/(@euclideU d)=> //.
by case: (edivzP m d)=> _ /(_ nz_d).
qed.

(* -------------------------------------------------------------------- *)
lemma modz_ge0 m d : d <> 0 => 0 <= m %% d.
proof.
case: (d = 0) => [->//|nz_d /=].
by case: (edivzP m d)=> _ /(_ nz_d) [].
qed.

(* -------------------------------------------------------------------- *)
lemma modn_ge0 m d : 0 <= m => 0 <= m %% d.
proof.
move=> ge0_m; case: (d = 0) => [->//|nz_d /=].
+ by rewrite (modz0 m). + by rewrite modz_ge0.
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
lemma modz_abs (m d : int): m %% `|d| = m %% d.
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

lemma pdiv_small n d: 0 <= n < d => n %/ d = 0.
proof. by move=> h; apply/divz_small => /#. qed.

lemma modz_small m d: 0 <= m < `|d| => m %% d = m.
proof. by move=> /emodz_eq /(_ 0). qed.

lemma pmod_small n d: 0 <= n < d => n %% d = n.
proof. by move=> h; apply/modz_small => /#. qed.

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
lemma oddP z: odd z <=> (z %% 2 <> 0).
proof.
rewrite {1}(divz_eq _ 2); case: (z %% 2 = 0) => /=.
+ by move=> ->/=; rewrite oddM odd2.
move=> nz_z2; suff ->/=: z %% 2 = 1.
+ by rewrite oddD oddM odd2 odd1.
by (have := ltz_pmod z 2 _; last have := modz_ge0 z 2 _) => // /#.
qed.

lemma oddPn z: !odd z <=> (z %% 2 = 0).
proof. by rewrite oddP /#. qed.

(* -------------------------------------------------------------------- *)
lemma modz_mod m d : m %% d %% d = m %% d.
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
lemma modz2 (a : int) : a %% 2 = b2i (odd a).
proof.
have eq_a_mod_2: (a %% 2 = 0) \/ (a %% 2 = 1) by smt(modz_ge0 ltz_pmod).
by case: (odd a) => [/oddP|/oddPn ->//]; case: eq_a_mod_2 => ->.
qed.

(* -------------------------------------------------------------------- *)
lemma divzMDl q m d : d <> 0 => (q * d + m) %/ d = q + (m %/ d).
proof.
move=> nz_d; have [+ /(_ nz_d) lt_md] - {1}-> := edivzP m d.
by rewrite addrA -mulrDl edivz_eq.
qed.

(* -------------------------------------------------------------------- *)
lemma divzMDr q m d : d <> 0 => (m + q * d) %/ d = q + (m %/ d).
proof. by move=> nz_d; rewrite (@addrC m); apply/divzMDl. qed.

(* -------------------------------------------------------------------- *)
lemma modzMDl p m d : (p * d + m) %% d = m %% d.
proof.
case: (d = 0) => [->|nz_d]; first by rewrite mulr0 add0r.
by rewrite modzE divzMDl // mulrDl opprD addrACA addrN -modzE.
qed.

(* -------------------------------------------------------------------- *)
lemma modzMDr p m d : (m + p * d) %% d = m %% d.
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
move=> d; case: (d = 0) => [->|]; first by rewrite /= !divz0.
rewrite eqr_le andaE negb_and -!ltrNge => -[/wl //|lt0_d gt0_p].
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

lemma modzDm m n d : (m %% d + n %% d) %% d = (m + n) %% d.
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

lemma modzBm m n d : (m %% d - n %% d) %% d = (m - n) %% d.
proof. by rewrite -modzDm -modzNm !modz_mod modzNm modzDm. qed.

lemma modz_prodm P F (s : 'a list) d :
  (BIM.big P (fun i => F i %% d) s) %% d = BIM.big P F s %% d.
proof.
elim: s => [|x s ih]; first by rewrite !BIM.big_nil.
rewrite !BIM.big_cons; case: (P x) => //.
by move=> _; rewrite modzMml -modzMmr ih modzMmr.
qed.

(* -------------------------------------------------------------------- *)
lemma mulz_modr p m d : 0 < p => p * (m %% d) = (p * m) %% (p * d).
proof. by move=> p_gt0; rewrite !modzE mulrBr divzMpl // mulrCA. qed.

lemma mulz_modl p m d : 0 < p => (m %% d) * p = (m * p) %% (d * p).
proof. by rewrite -!(mulrC p); apply/mulz_modr. qed.

(* -------------------------------------------------------------------- *)
lemma dvdzE d m : d %| m <=> (m %% d = 0).
proof. by []. qed.

lemma dvdz0 d : d %| 0.
proof. by rewrite dvdzE mod0z. qed.

lemma dvd0z m : 0 %| m <=> m = 0.
proof. by rewrite dvdzE modz0. qed.

lemma dvd1z m : 1 %| m.
proof. by rewrite dvdzE modz1. qed.

hint exact : dvd1z.

lemma dvdz1 d : d %| 1 <=> `|d| = 1.
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

lemma dvdzz m : m %| m.
proof. by rewrite dvdzE modzz. qed.

lemma dvdzP d m : (d %| m) <=> (exists q, m = q * d).
proof.
rewrite dvdzE; split=> [|[q->]]; last by rewrite modzMl.
by move=> eq; exists (m %/ d); rewrite {1}(divz_eq m d) eq.
qed.

lemma dvdz_mull d m n : d %| n => d %| m * n.
proof. by move/dvdzP=> [q ->]; rewrite dvdzE mulrA modzMl. qed.

lemma dvdz_mulr d m n : d %| m => d %| m * n.
proof. by move=> d_m; rewrite mulrC dvdz_mull. qed.

lemma dvdz_mul d1 d2 m1 m2 :
  d1 %| m1 => d2 %| m2 => d1 * d2 %| m1 * m2.
proof.
move=> /dvdzP[q1 ->] /dvdzP[q2 ->].
by rewrite mulrCA -mulrA 2?dvdz_mull // dvdzz.
qed.

lemma dvdz_trans n d m : d %| n => n %| m => d %| m.
proof. by move=> dv_dn /dvdzP[q ->]; apply/dvdz_mull. qed.

lemma dvdz_le m n : n <> 0 => m %| n => `|m| <= `|n|.
proof.
move=> nz_n /dvdzP [q ^nE ->]; rewrite normrM.
case: (m = 0) => [->//|nz_m]; rewrite ler_pmull 1:normr_gt0 //.
have := normr_ge0 q; rewrite ler_eqVlt => -[|].
+ by rewrite eq_sym normr0P => ->>; move: nE nz_n.
+ by rewrite ltzE.
qed.

lemma dvdn_le m n : 0 < n => m %| n => m <= n.
proof. smt(dvdz_le). qed.

lemma dvdz_oddr (a b : int) : odd b => a %| b => odd a.
proof. by move=> odd_b /dvdzP[q ->>]; rewrite oddM /# in odd_b. qed.

lemma dvdz_norml (a b : int) : (`|a| %| b) <=> (a %| b).
proof. by rewrite /(%|) modz_abs. qed.

(* -------------------------------------------------------------------- *)
lemma dvdzD d m1 m2 : d %| m1 => d %| m2 => d %| (m1 + m2).
proof.
by move=> /dvdzP[q1 ->] /dvdzP[q2 ->]; rewrite -mulrDl &(dvdz_mull) dvdzz.
qed.

lemma dvdzN d m : d %| m => d %| -m.
proof. by move/dvdzP=> [q ->]; rewrite -mulNr &(dvdz_mull) dvdzz. qed.

lemma dvdzB d m1 m2 : d %| m1 => d %| m2 => d %| (m1 - m2).
proof. by move=> h1 h2; apply/dvdzD/dvdzN. qed.

(* -------------------------------------------------------------------- *)
lemma dvdz_eq d m : (d %| m) <=> (m %/ d * d = m).
proof. by rewrite dvdzE modzE subr_eq0 eq_sym. qed.

lemma dvdz_exp2l p m n : 0 <= m <= n => (p ^ m %| p ^ n).
proof.
move=> [ge0_m le_mn]; rewrite dvdzE; rewrite -(subrK n m).
by rewrite exprD_nneg ?subr_ge0 // modzMl.
qed.

(* -------------------------------------------------------------------- *)
lemma dvdz_modzDl (m n d : int) : d %| m => (m + n) %% d = n %% d.
proof. by rewrite -modzDml=> /dvdzE ->. qed.

lemma dvdz_modzDr (m n d : int) : d %| n => (m + n) %% d = m %% d.
proof. by rewrite -modzDmr=> /dvdzE ->. qed.

lemma eqz_mod_dvd (a b c : int) : (a %| (b - c)) <=> (b %% a = c %% a).
proof.
rewrite dvdzE; split=> heq.
- by rewrite -(subrK b c) -modzDml heq.
- by rewrite -modzDml heq modzDml subrr mod0z.
qed.

(* -------------------------------------------------------------------- *)
lemma modz_dvd m p q: q %| p => (m %% p) %% q = m %% q.
proof.
move=> dv_qp; rewrite (modzE _ p) -mulNr.
by move/dvdz_eq: dv_qp=> {2}<-; rewrite mulrA modzMDr.
qed.

(* -------------------------------------------------------------------- *)
lemma divNz (m d : int) :
  0 < m => 0 < d => (-m) %/ d = - ((m-1) %/ d + 1).
proof.
move=> gt0_m gt0_d; rewrite !edivz_def.
rewrite oppr_ge0 lerNgt gt0_m -ltzS -addrA gt0_m /=.
rewrite opprD opprK; case _: (edivn _ _) => q r E /=.
by rewrite mulrN signz_gt0.
qed.

lemma modNz m d : 0 < m => 0 < d =>
  (-m) %% d = d - 1 - (m-1) %% d.
proof. by move=> gt0_m gt0_d; rewrite !modzE !divNz //; ring. qed.

(* -------------------------------------------------------------------- *)
lemma dvdz_normr (a b : int) : (a %| `|b|) <=> (a %| b).
proof.
case: (0 <= b) => [ge0_b|]; first by rewrite ger0_norm.
move/ltrNge/ltrW => le0_b; rewrite ler0_norm //.
by split; move/dvdzN; rewrite ?opprK.
qed.

(* -------------------------------------------------------------------- *)
lemma divzK d m : d %| m => m %/ d * d = m.
proof. by move/dvdz_eq. qed.

(* -------------------------------------------------------------------- *)
lemma divMr p q m : m %| q => (p * q) %/ m = p * (q %/ m).
proof.
case: (m = 0) => [-> /dvd0z ->|nz_m]; first by rewrite !div0z.
by case/dvdzP=> [k ->]; rewrite mulrA !mulzK.
qed.

lemma lez_floor m d : d <> 0 => m %/ d * d <= m.
proof. by rewrite -subr_ge0 -modzE; apply/modz_ge0. qed.

lemma ltz_ceil m d : 0 < d => m < (m %/ d + 1) * d.
proof.
by move=> d_gt0; rewrite mulrDl mul1r -ltr_subl_addl -modzE ltz_pmod.
qed.

lemma ltz_divLR m n d : 0 < d => (m %/ d < n) <=> (m < n * d).
proof.
move=> d_gt0; split.
  rewrite -lez_add1r addrC -(ler_pmul2r _ d_gt0).
  by apply/ltr_le_trans/ltz_ceil.
rewrite -(ltr_pmul2r _ d_gt0 _ n) //; apply/ler_lt_trans.
by apply/lez_floor; rewrite gtr_eqF.
qed.

lemma lez_divRL m n d : 0 < d =>
  (m <= n %/ d) <=> (m * d <= n).
proof. by move=> d_gt0; rewrite !lerNgt ltz_divLR. qed.

lemma lez_divLR d m n : 0 < d => d %| m =>
  (m %/ d <= n) <=> (m <= n * d).
proof. by move=> /ler_pmul2r <- /divzK->. qed.

lemma ltz_divRL d m n : 0 < d => d %| m =>
  (n < m %/ d) <=> (n * d < m).
proof. by move=> /ltr_pmul2r <- /divzK->. qed.

lemma eqz_div d m n : d <> 0 => d %| m =>
  (n = m %/ d) <=> (n * d = m).
proof. by move=> /mulIf/inj_eq <- /divzK /= ->. qed.

lemma eqz_mul d m n : d <> 0 => d %| m =>
  (m = n * d) <=> (m %/ d = n).
proof. by move=> d_gt0 dv_d_m; rewrite eq_sym -eqz_div // eq_sym. qed.

lemma divz_eqP (m d n : int) :
  0 < d => m %/ d = n <=> n * d <= m < (n + 1) * d.
proof.
  move => lt0d; split => [<<-|[le_m ltm_]].
  + by split => [|_]; [apply/lez_floor/gtr_eqF|apply/ltz_ceil].
  by apply/eqz_leq; split; [apply/ltzS/ltz_divLR|apply/lez_divRL].
qed.

lemma leq_div2r (d m n : int) :
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

lemma leq_trunc_div m d : 0 <= m => 0 <= d => m %/ d * d <= m.
proof.
move=> ge0_m ge0_d; rewrite {2}(divz_eq m d).
by rewrite ler_paddr // modn_ge0.
qed.

lemma leq_div m d : 0 <= m => 0 <= d => m %/ d <= m.
proof.
move=> ge0_m; rewrite ler_eqVlt => -[<-|]; 1: by rewrite divz0.
move=> gt0_d; rewrite -(ler_pmul2r d) //.
apply/(ler_trans m); first by apply/leq_trunc_div/ltrW.
by apply/ler_pemulr => //; rewrite -(ltzE 0).
qed.

lemma lez_div m d : `|m %/ d| <= `|m|.
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
lemma divzDl m n d : d %| m => (m + n) %/ d = (m %/ d) + (n %/ d).
proof.
case: (d = 0) => [->|nz_d]; first by rewrite !divz0.
by move/divzK=> {1}<-; rewrite divzMDl.
qed.

lemma divzDr m n d : d %| n => (m + n) %/ d = (m %/ d) + (n %/ d).
proof. by move=> dv_n; rewrite addrC divzDl // addrC. qed.

lemma divz_mulp (n d1 d2 : int) : 
  0 < d1 =>
  0 < d2 =>
  n %/ (d1 * d2) = n %/ d1 %/ d2.
proof.
  move => lt0d1 lt0d2; rewrite (mulzC d1); apply divz_eqP; [by apply mulr_gt0|split => [|_]].
  + by rewrite mulrA; apply (lez_trans (n %/ d1 * d1));
    [apply/ler_pmul2r => //|]; apply/lez_floor/gtr_eqF.
  by rewrite mulrA; apply (ltr_le_trans ((n %/ d1 + 1) * d1));
  [|apply/ler_pmul2r => //; apply/ltzE]; apply/ltz_ceil.
qed.

lemma divz_mul (n d1 d2 : int) :
  0 <= d1 =>
  n %/ (d1 * d2) = n %/ d1 %/ d2.
proof.
move => /lez_eqVlt [<<- //=|lt0d1];
(case (0 <= d2) => [/lez_eqVlt [<<- //=|lt0d2]|/ltzNge ltd20]).
(*FIXME: why no automatic rewriting here for divz0 and div0z?*)
+ by rewrite !divz0.
+ by rewrite !divz0 div0z.
+ by rewrite !divz0 div0z.
+ by rewrite !divz0.
+ by rewrite divz_mulp.
by rewrite -(oppzK d2) mulrN 2!divzN eqr_opp divz_mulp // ltr_oppr.
qed.

lemma divzpMr p m d : d %| m => p * (m %/ d) = p * m %/ d.
proof. by move => /dvdzP [q ->>]; case (d = 0) => [->> /=|neqd0]; [rewrite divz0|rewrite mulrA !mulzK]. qed.

lemma dvdNdiv x y : x <> 0 => x %| y => (-y) %/ x = - y %/ x.
proof. by move => neqx0 /dvdzP [z ->>]; rewrite -mulNr !mulzK. qed.

lemma exprD_subz (x m n : int) : x <> 0 => 0 <= n <= m => x ^ (m - n) = (x ^ m) %/ (x ^ n).
proof.
move => neqx0 [le0n lenm]; rewrite eq_sym -(eqz_mul (x ^ n) (x ^ m) (x ^ (m - n))).
+ by move: neqx0; rewrite implybNN expf_eq0.
+ by apply dvdz_exp2l.
by rewrite -exprD_nneg ?subrK // ler_subr_addr.
qed.

lemma expz_div (x n m : int) :
  0 <= m <= n => 0 < x => x^n %/ x^m = x^(n-m).
proof.
move=> [ge0_m le_mn] gt0_x; rewrite -{1}(subrK n m).
by rewrite exprD_nneg 1:subr_ge0 // mulzK // expf_eq0 (@gtr_eqF x).
qed.

(* ==================================================================== *)
lemma oddW (a : int) : odd a => exists a', a = 2 * a' + 1.
proof.
move/oddP=> nz_mod2; exists (a %/ 2).
rewrite mulrC divzE (_ : a %% 2 = 1) //.
suff: 0 <= a %% 2 < 2 by smt().
by rewrite modz_ge0 // ltz_pmod.
qed.

lemma oddWn (a : int) : !odd a => exists a', a = 2 * a'.
proof.
move/oddPn=> z_mod2; exists (a %/ 2).
by rewrite mulrC divzE z_mod2.
qed.

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
+ by rewrite {2}[b]signzE dvdz_mull dvdzz.
+ by move=> x _ xDb; rewrite (ler_trans `|x|) 1:ler_norm dvdz_le.
move=> nz_a; have nz_b : b <> 0.
+ by apply: contraL le_ab => ->; rewrite normr0 lerNgt /= normr_gt0.
pose E := fun z => (`|a * b| - z) %| a /\ (`|a * b| - z %| b).
have ge0_pE: 0 <= `|a * b| - 1.
+ have := normr_ge0 (a * b); rewrite subr_ge0 ler_eqVlt.
  rewrite ltzE /= => -[] //; rewrite eq_sym.
  by rewrite normrM mulf_eq0 !normr0P !(nz_a, nz_b).
have pE: E (`|a * b| - 1); first move=> @/E /=; do! split.
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

lemma gcdP a b : (a, b) <> (0, 0) =>
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

lemma gcd_uniq a b z : (a, b) <> (0, 0) =>
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
+ by rewrite {2}[a]signzE dvdz_mull dvdzz.
+ by move=> x _ xDa; rewrite &(ler_trans `|x|) 1:ler_norm dvdz_le.
qed.

lemma gcdz0 a : gcd a 0 = `|a|.
proof. by rewrite gcdC gcd0z. qed.

hint simplify gcd0z, gcdz0.

lemma gcd1z a : gcd 1 a = 1.
proof.
apply/eq_sym/gcd_uniq => // x.
by rewrite dvdz1 => <- _; rewrite ler_norm.
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

lemma Bachet_Bezout (a b : int) :
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

(* -------------------------------------------------------------------- *)
lemma dvdz_gcd (a b c : int) :
  a %| b => a %| c => a %| gcd b c.
proof.
move=> dvd_ab dvd_ac; case: (Bachet_Bezout b c) => u v <-.
by rewrite dvdzD dvdz_mull.
qed.

(* -------------------------------------------------------------------- *)
lemma mulz_gcdr a b c : `|a| * gcd b c = gcd (a * b) (a * c).
proof.
wlog: a / (0 <= a) => [wlog|].
- case: (0 <= a); first by apply: wlog.
  move/ltrNge/ltrW => le0_a; have := wlog (-a) _; ~-1:smt().
  by rewrite normrN !mulNr !(gcdNz, gcdzN).
rewrite ler_eqVlt => -[<<-|gt0_a]; first by rewrite normr0.
case: (b = 0) => [->> /=|nz_b]; first by rewrite normrM.
case: (c = 0) => [->> /=|nz_c]; first by rewrite normrM.
rewrite gtr0_norm //; apply: gcd_uniq; 1,2: smt(ge0_gcd).
- by rewrite dvdz_mul -1:dvdz_gcdl dvdzz.
- by rewrite dvdz_mul -1:dvdz_gcdr dvdzz.
move=> z z_ab z_ac; suff: z %| a * gcd b c.
- apply/dvdn_le/mulr_gt0 => //.
  by rewrite ltr_neqAle ge0_gcd /= eq_sym gcd_eq0 /#.
case: (Bachet_Bezout b c) => u v <-.
by rewrite mulrDr !(mulrCA a) dvdzD dvdz_mull.
qed.

(* -------------------------------------------------------------------- *)
lemma mulz_gcdl a b c : gcd b c * `|a| = gcd (b * a) (c * a).
proof. by rewrite mulrC mulz_gcdr ![a * _]mulrC. qed.


(* ==================================================================== *)
abbrev [-printing] eqm m a b = a %% m = b %% m.

(* -------------------------------------------------------------------- *)
lemma eqmodE (m a b : int) :
  eqm m a b <=> (m %| (b - a)).
proof. by rewrite eqz_mod_dvd /#. qed.

(* -------------------------------------------------------------------- *)
lemma eqmodP (m a b : int) :
  eqm m a b <=> (exists c, b - a = c * m).
proof. by rewrite eqmodE dvdzP. qed.

(* -------------------------------------------------------------------- *)
lemma eqm_refl (m a : int) : eqm m a a.
proof. by done. qed.

(* -------------------------------------------------------------------- *)
lemma eqmC (m a b : int) : eqm m a b => eqm m b a.
proof. by move/eq_sym. qed.

(* -------------------------------------------------------------------- *)
lemma eqm_trans (m b a c : int) : eqm m a b => eqm m b c => eqm m a c.
proof. by move=> ->. qed.

(* -------------------------------------------------------------------- *)
lemma eqmN (m a b : int) : eqm m a b => eqm m (-a) (-b).
proof.
case/eqmodP=> [k eq]; apply/eqmodP; exists (-k).
by rewrite -opprD eq mulNr.
qed.

(* -------------------------------------------------------------------- *)
lemma eqmD (m a1 b1 a2 b2 : int) :
  eqm m a1 b1 => eqm m a2 b2 => eqm m (a1 + a2) (b1 + b2).
proof.
move=> /eqmodP[k1 eq1] /eqmodP[k2 eq2]; apply/eqmodP.
by exists (k1 + k2); rewrite subrACA !(eq1, eq2) -mulrDl.
qed.

(* -------------------------------------------------------------------- *)
lemma eqmB (m a1 b1 a2 b2 : int) :
  eqm m a1 b1 => eqm m a2 b2 => eqm m (a1 - a2) (b1 - b2).
proof. by move=> *; apply/eqmD => //; apply/eqmN. qed.

(* -------------------------------------------------------------------- *)
lemma eqmM (m a1 b1 a2 b2 : int) :
  eqm m a1 b1 => eqm m a2 b2 => eqm m (a1 * a2) (b1 * b2).
proof.
by move=> eq1 eq2; rewrite -modzMml -modzMmr eq1 eq2 modzMml modzMmr.
qed.

(* ==================================================================== *)
op coprime a b = gcd a b = 1.

(* -------------------------------------------------------------------- *)
lemma Bezout (a b : int) : coprime a b =>
  exists u v, u * a + v * b = 1.
proof. by move=> @/coprime <-; apply: Bachet_Bezout. qed.

(* -------------------------------------------------------------------- *)
lemma Gauss (a b c : int) : a %| (b * c) => coprime a b => a %| c.
proof.
move=> a_div_bc eq1_gcd_ab; suff: a %| gcd (a * c) (b * c).
- by rewrite -mulz_gcdl eq1_gcd_ab /= dvdz_normr.
by apply: dvdz_gcd => //; apply/dvdz_mulr/dvdzz.
qed.

(* -------------------------------------------------------------------- *)
lemma coprimeP (a b : int) :
  coprime a b <=> exists u v, u * a + v * b = 1.
proof.
split; [exact/Bezout | case=> u v eq @/coprime].
apply/eq_sym/gcd_uniq; ~-1: move=> //#.
move=> x dvd_xa dvd_xb; have: x %| (u * a + v * b).
- by rewrite dvdzD ?dvdz_mull.
by rewrite eq => /dvdz1 /#.
qed.

(* -------------------------------------------------------------------- *)
lemma coprime_sym (a b : int) : coprime a b <=> coprime b a.
proof. by rewrite /coprime gcdC. qed.

(* -------------------------------------------------------------------- *)
lemma coprime_modl (a b : int) : coprime (a %% b) b = coprime a b.
proof. by rewrite /coprime gcd_modl. qed.

lemma coprime_modr (a b : int) : coprime a (b %% a) = coprime a b.
proof. by rewrite /coprime gcd_modr. qed.

(* -------------------------------------------------------------------- *)
lemma coprime1z (a : int) : coprime 1 a.
proof. done. qed.

hint exact : coprime1z.

(* -------------------------------------------------------------------- *)
lemma coprimez1 (a : int) : coprime a 1.
proof. done. qed.

hint exact : coprime1z.

(* -------------------------------------------------------------------- *)
lemma coprime2z (a : int) : coprime 2 a <=> odd a.
proof. by rewrite -coprime_modr modz2; case: (odd a). qed.

(* -------------------------------------------------------------------- *)
lemma coprimez2 (a : int) : coprime a 2 <=> odd a.
proof. by rewrite coprime_sym coprime2z. qed.

(* -------------------------------------------------------------------- *)
lemma coprimeSz (a : int) : coprime (a + 1) a.
proof. rewrite addrC -coprime_modl (modzDr 1) coprime_modl coprime1z. qed.

(* -------------------------------------------------------------------- *)
lemma coprimezS (a : int) : coprime a (a + 1).
proof. by rewrite coprime_sym coprimeSz. qed.

(* -------------------------------------------------------------------- *)
lemma modz_coprime k m : (exists u, (k * u) %% m = 1) => coprime k m.
proof.
case=> u eq; have nz_k: k <> 0.
- by apply: contraL eq => -> /=; rewrite mod0z.
apply/coprimeP; exists u (-(k * u %/ m)).
by rewrite mulrC mulNr divzE eq #ring.
qed.

(* -------------------------------------------------------------------- *)
lemma Gauss_dvdr (a b c : int) : coprime a b => (a %| b * c) <=> (a %| c).
proof. by move=> cop_a_b; split; [move/Gauss; apply | apply: dvdz_mull]. qed.

(* -------------------------------------------------------------------- *)
lemma Gauss_dvdl (a b c : int) : coprime a c => (a %| b * c) <=> (a %| b).
proof. by move=> ?; rewrite mulrC; apply: Gauss_dvdr. qed.

(* -------------------------------------------------------------------- *)
lemma Gauss_gcdr (c a b : int) : coprime c a => gcd c (a * b) = gcd c b.
proof.
case: ((c, a * b) = (0, 0)) => [[] -> //#|nz_c].
move=> cop_c_a; apply/eq_sym/gcd_uniq => //.
- by apply/dvdz_mull/dvdz_gcdr.
move=> x dvd_x_c dvd_x_aMb; apply: gcd_max; ~-1: move=> //#.
suff: coprime x a by move/Gauss_dvdr; apply.
case/coprimeP: cop_c_a => u v eq; apply/coprimeP.
by case/dvdzP: dvd_x_c => q ->>; exists (u * q) v; ring eq.
qed.

(* -------------------------------------------------------------------- *)
lemma Gauss_gcdl (c a b : int) : coprime c b => gcd c (a * b) = gcd c a.
proof. by move=> ?; rewrite mulrC &(Gauss_gcdr). qed.

(* -------------------------------------------------------------------- *)
lemma coprimeMr (c a b : int) : coprime c (a * b) <=> (coprime c a /\ coprime c b).
proof.
case: (coprime c a) => /= cop_c_a; first by rewrite /coprime Gauss_gcdr.
apply: contra cop_c_a => /coprimeP [u v] eq; apply/coprimeP.
by exists u (v * b); ring eq.
qed.

(* -------------------------------------------------------------------- *)
lemma coprimeMl (c a b : int) : coprime (a * b) c <=> (coprime a c /\ coprime b c).
proof. by rewrite coprime_sym coprimeMr ![coprime c _]coprime_sym. qed.

(* -------------------------------------------------------------------- *)
lemma coprime_dvdl (a b c : int) : a %| b => coprime b c => coprime a c.
proof. by case/dvdzP=> q -> /coprimeMl. qed.

(* -------------------------------------------------------------------- *)
lemma coprime_dvdr (a b c : int) : a %| b => coprime c b => coprime c a.
proof. by rewrite !(coprime_sym c); apply: coprime_dvdl. qed.

(* -------------------------------------------------------------------- *)
lemma modinv p a : coprime p a => exists b, p %| (a * b - 1)%Int.
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
lemma eqmV (m c : int) : 1 < m => coprime m c => eqm m (c * invm c m) 1.
proof. by move=> gt1_m cop_m_c; rewrite (pmod_small 1 m) // &(invmP). qed.

(* -------------------------------------------------------------------- *)
lemma eqmZI (m a b c : int) :
  1 < m => coprime m c => eqm m (c * a) (c * b) => eqm m a b.
proof.
move=> gt1_m cop_m_c eq1; have eq2 := eqm_refl m (invm c m).
have := eqmM _ _ _ _ _ eq1 eq2; rewrite ![(_ * _)%Int * (invm _ _)]mulrAC.
move=> {eq1 eq2} eq; apply: (eqm_trans _ (c * invm c m * a)).
- by rewrite -{1}[a]mul1r; apply: eqmM => //; apply/eqmC/eqmV.
- apply: (eqm_trans _ _ _ _ eq); rewrite -{2}[b]mul1r.
  by apply: eqmM => //; apply/eqmV.
qed.

(* ==================================================================== *)
op prime a = 1 < a /\ (forall q, q %| a => `|q| = 1 \/ `|q| = a).

lemma gt1_prime p : prime p => 1 < p.
proof. by case. qed.

lemma gt0_prime p : prime p => 0 < p.
proof. by move/gt1_prime/(ltr_trans _ _ _ ltr01). qed.

lemma prime_coprime p : prime p =>
  forall a, a %% p <> 0 => coprime p a.
proof.
move=> pm_p a nz_a; have h := dvdz_gcdl p a.
case: pm_p => gt1_p /(_ _ h) => {h}; rewrite ger0_norm ?ge0_gcd.
case=> // /eq_sym pE; have: p %| a  by rewrite {1}pE dvdz_gcdr.
by rewrite dvdzE nz_a.
qed.

(* -------------------------------------------------------------------- *)
lemma prime2 : prime 2.
proof.
split=> // q dvd_q2; have := dvdz_le _ _ _ dvd_q2 => //.
by case: (q = 0) => [->>|/#]; rewrite dvd0z in dvd_q2.
qed.

hint exact : prime2.

(* -------------------------------------------------------------------- *)
lemma modinv_prime p : prime p =>
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

(* -------------------------------------------------------------------- *)
lemma uniq_invm (m a v1 v2 : int): 1 < m =>
  a * v1 %% m = 1 => a * v2 %% m = 1 => v1 %% m = v2 %% m.
proof.
move=> gt1_m; case: (a = 0) => [->/=|nz_a]; first by rewrite mod0z.
move=> ^eq1 + ^eq2 + - <- /eqmC.
have := eqmZI m v1 v2 a _ _ => //.
by apply/coprime_sym/modz_coprime; exists v1.
qed.

(* -------------------------------------------------------------------- *)
lemma Euclide (a b c : int) :
  a %| (b * c) => prime a => a %| b \/ a %| c.
proof.
move=> a_div_bc prime_a; case: (a %| b) => //=.
move=> Ndvd_ab; suff: coprime a b by apply: Gauss.
by apply: prime_coprime.
qed.

(* -------------------------------------------------------------------- *)
lemma Euclide_prod F (s : 'a list) a :
  a %| BIM.big predT F s => prime a =>
    exists x, x \in s /\ a %| F x.
proof.
elim: s => [|x s ih]; first by rewrite BIM.big_nil; smt(dvdz_le).
rewrite BIM.big_cons ifT // => + prime_a - /Euclide /(_ prime_a).
case=> [dvd_a_Fx|dvd_ih]; first by exists x.
case: (ih dvd_ih prime_a) => y [y_in_s dvd_a_Fy].
by exists y; split=> //; rewrite in_cons y_in_s.
qed.

(* ==================================================================== *)
lemma sumidE n : 0 <= n =>
  sumid 0 n = (n * (n - 1)) %/ 2.
proof. by move/Bigint.sumidE_r=> <-; rewrite mulKz. qed.

(* -------------------------------------------------------------------- *)
import Bigint.BIM.

lemma Fermat_little (p a : int) :
   prime p => ! (p %| a) => p %| (exp a (p - 1) - 1).
proof.
move=> prime_p N_p_div_a; pose N := fact (p-1) * exp a (p-1).
have gt0_p: 0 < p by smt(gt1_prime).
suff: p %| (fact (p-1) * (exp a (p-1) - 1)).
- move/Euclide => /(_ prime_p) -[] // /Euclide_prod /(_ prime_p) /=.
  by case=> x [] /mem_range rg_x @/idfun; smt(dvdz_le).
rewrite mulrDr mulrN1 eqz_mod_dvd -/N (_ : N = bigi predT (fun i => i * a) 1 p).
- rewrite /N /fact /= BIM.big_split mulr_const; do 2? congr => //.
  by rewrite size_range /#.
move=> {N}; rewrite -modz_prodm /=; do! congr.
rewrite -(big_mapT _ idfun) &(eq_big_perm) /= uniq_perm_eq_size.
- apply: map_inj_in_uniq => /=; last by apply: range_uniq.
  move=> x y /mem_range rgx /mem_range rgy.
  rewrite -eqz_mod_dvd -mulrBl => /Euclide /(_ prime_p).
  by rewrite N_p_div_a /= eqz_mod_dvd !modz_small //#.
- by apply: range_uniq.
- by rewrite size_map.
- move=> x /mapP [y] [/mem_range nz_y ->] /=; rewrite mem_range.
  rewrite ltz_pmod //= (lez_add1r 0) ltr_neqAle.
  rewrite modz_ge0 1:gtr_eqF //= eq_sym -dvdzE.
  by apply/negP => /Euclide /(_ prime_p); smt(dvdn_le).
qed.

(* ==================================================================== *)
(* FIXME: should be supersed by IntDiv                                  *)
lemma modz_dvd_pow n p i k:
  0 <= n <= p => i %% k^p %% k^n = i %% k^n.
proof. by move=> le_np; apply/modz_dvd/dvdz_exp2l. qed.

lemma modz_pow_split n p i k : 0 <= p <= n =>
   i = i %/ k^n * k^n + (i %% k^n %/ k^p) * k^p + i %% k^p.
proof.
move=> lt_pn; rewrite {1}(divz_eq i (k^n)); rewrite -addrA; congr.
by rewrite {1}(divz_eq (i %% k^n) (k^p)) modz_dvd_pow.
qed.

lemma dvdz_mod_div d1 d2 m :
  0 < d1 =>
  0 < d2 =>
  d2 %| d1 =>
  m %% d1 %/ d2 = (m %/ d2) %% (d1 %/ d2).
proof.
  move => lt0d1 lt0d2 /dvdzP [q ->>]; rewrite modzE mulrA -mulNr mulzK; first by rewrite gtr_eqF.
  rewrite divzMDr //; first by rewrite gtr_eqF.
  rewrite addrC modzE; do 2!congr.
  by rewrite (mulrC q) divz_mulp // -(pmulr_lgt0 _ _ lt0d2).
qed.

lemma modz_pow_div x n p m :
  0 < x =>
  0 <= p <= n =>
  m %% x ^ n %/ x ^ p = (m %/ x ^ p) %% (x ^ (n - p)).
proof.
  by move => lt0x [le0p lepn]; rewrite dvdz_mod_div //;
  [apply expr_gt0|apply expr_gt0|apply dvdz_exp2l|rewrite exprD_subz // gtr_eqF].
qed.

lemma modz_pow2_div n p m :
  0 <= p <= n =>
  m %% 2 ^ n %/ 2 ^ p = (m %/ 2 ^ p) %% (2 ^ (n - p)).
proof. by apply modz_pow_div. qed.

(* ==================================================================== *)
lemma pow_normr (p x : int) :
  p ^ x = p ^ `|x|.
proof.
by rewrite normE; case (0 <= x) => //; rewrite exprN. qed.

lemma lt_pow (p x : int) :
  1 < p =>
  x < p ^ x.
proof.
  move => lt1p; case (0 <= x) => [|/ltzNge ltx0]; last by apply/(ltr_le_trans _ _ _ ltx0)/expr_ge0/ltzW/ltzE/ltzW.
  elim x => [|x le0x ltxpow]; first by rewrite expr0.
  apply/(ler_lt_trans (p ^ x)); first by apply/ltzE.
  by rewrite exprSr // ltr_pmulr // expr_gt0 ltzE ltzW.
qed.

lemma Ndvd_pow (p x : int) :
  1 < `|p| =>
  x <> 0 =>
  ! p ^ x %| x.
proof.
  move => lt1norm neqx0; apply/negP => dvdpowx.
  move: (dvdz_le _ _ _ dvdpowx) => //.
  rewrite pow_normr normrX_nat ?normr_ge0 //; apply/negP/ltzNge.
  by apply/lt_pow.
qed.

lemma dvdz2_eq m n :
  0 <= m =>
  0 <= n =>
  m %| n =>
  n %| m =>
  m = n.
proof.
  move => le0m le0n /dvdzP [x ->>] /dvdzP [y /(congr1 (transpose (%/) m) _ _) /=].
  rewrite mulrA divzz; case (m = 0) => /= [->> //=|neqm0]. 
  rewrite /b2i mulzK //= => eq1mul; move: (unitrM y x); move: eq1mul => <- /=.
  move => [_ [|] ->> //=]; move: le0n; rewrite mulNr /= oppr_ge0 => lem0.
  by move: neqm0; rewrite eqz_leq lem0 le0m.
qed.

lemma dvd_le_pow (p m n : int) :
  1 < `|p| =>
  p ^ m %| p ^ n =>
  `|m| <= `|n|.
proof.
  rewrite (pow_normr p m) (pow_normr p n) => lt1norm dvdpow2.
  have:= (dvdz_le _ _ _ dvdpow2); first by rewrite expf_eq0 -negP => -[_ ->>].
  rewrite !normrX_nat ?normr_ge0 //.
  by apply ler_weexpn2r => //; apply normr_ge0.
qed.

lemma le_dvd_pow (p m n : int) :
  `|m| <= `|n| =>
  p ^ m %| p ^ n.
proof.
  rewrite (pow_normr p m) (pow_normr p n) => lenormr2.
  apply/dvdzP; exists (p ^ (`|n| - `|m|)).
  by rewrite -exprD_nneg; [apply subr_ge0|apply normr_ge0|rewrite -addrA].
qed.

(*-----------------------------------------------------------------------------*)

lemma eq_range m n : m = n <=> m \in range n (n+1).
proof. by rewrite mem_range ltzS eqz_leq. qed.

lemma range_div_range m d min max : 0 < d => m %/ d \in range min max <=> m \in range (min * d) (max * d).
proof.
move => lt0d; rewrite !mem_range !andabP; apply andb_id2.
+ by apply lez_divRL.
by rewrite -ltz_divLR // ltzS.
qed.

lemma eq_div_range m d n : 0 < d => m %/ d = n <=> m \in range (n * d) ((n + 1) * d).
proof. by move => lt0d; rewrite eq_range range_div_range. qed.

(*-----------------------------------------------------------------------------*)
abbrev (%\) (m d : int) : int = - ((- m) %/ d).

lemma lez_ceil m d : d <> 0 => m <= m %\ d * d.
proof. by rewrite mulNr => neqd0; apply/ler_oppr/lez_floor. qed.

lemma ltz_floor m d : 0 < d => (m %\ d - 1) * d < m.
proof. by rewrite -opprD mulNr => lt0d; apply/ltr_oppl/ltz_ceil. qed.

lemma lez_NdivNLR (d m n : int) : 0 < d => d %| n => m <= n %\ d <=> m * d <= n.
proof.
move => lt0d dvddn; rewrite ler_oppr lez_divLR //; first by apply dvdzN.
by rewrite mulNr ler_opp2.
qed.

lemma lez_NdivNRL (m n d : int) : 0 < d => m %\ d <= n <=> m <= n * d.
proof. by move => lt0d; rewrite ler_oppl lez_divRL // mulNr ler_opp2. qed.

lemma ltz_NdivNLR (m n d : int) : 0 < d => m < n %\ d <=> m * d < n.
proof. by move => lt0d; rewrite ltr_oppr ltz_divLR // mulNr ltr_opp2. qed.

lemma ltz_NdivNRL (d m n : int) : 0 < d => d %| m => m %\ d < n  <=> m < n * d.
move => lt0d dvddm; rewrite ltr_oppl ltz_divRL //; first by apply dvdzN.
by rewrite mulNr ltr_opp2.
qed.

(*-----------------------------------------------------------------------------*)

lemma mem_range_mull (m n x y : int) :
  0 < x =>
  x * y \in range m n <=> y \in range (m %\ x) (n %\ x).
proof. by move => lt0x; rewrite !mem_range lez_NdivNRL // ltz_NdivNLR // !(mulrC y). qed.

lemma mem_range_mulr (m n x y : int) :
  0 < y =>
  x * y \in range m n <=> x \in range (m %\ y) (n %\ y).
proof. by rewrite mulrC; apply/mem_range_mull. qed.

lemma mem_range_mod (x y : int) :
  y <> 0 =>
  x %% y \in range 0 `|y|.
proof. by move => neqy0; rewrite mem_range modz_ge0 // ltz_mod. qed.

lemma mem_range_add_mul (m n l x y : int) :
  x \in range 0 l =>
  y \in range m n =>
  x + l * y \in range (m * l) (n * l).
proof.
  move => Hx_range Hy_range; rewrite mem_range_addl mem_range_mull; first by apply/(ler_lt_trans x); move/mem_range: Hx_range.
  move: Hy_range; apply/mem_range_incl.
  + rewrite lez_NdivNRL; first by apply/(ler_lt_trans x); move/mem_range: Hx_range.
    by rewrite ler_subl_addr ler_addl; move/mem_range: Hx_range.
  rewrite -ltzS -ltr_subl_addr ltz_NdivNLR; first by apply/(ler_lt_trans x); move/mem_range: Hx_range.
  by rewrite mulrDl mulNr /= ler_lt_sub //; move/mem_range: Hx_range.
qed.

lemma mem_range_add_mul_eq (x1 y1 x2 y2 l : int) :
  x1 \in range 0 l =>
  x2 \in range 0 l =>
  x1 + l * y1 = x2 + l * y2 <=>
  x1 = x2 /\ y1 = y2.
proof.
  move => /mem_range [le0x1 ltx1l] /mem_range [le0x2 ltx2l]; split => [Heq|[->> ->>] //]; split.
  + move: (congr1 (transpose (%%)%IntID l) _ _ Heq) => /=.
    by rewrite !(mulrC l) !modzMDr !pmod_small.
  move: (congr1 (transpose (%/)%IntID l) _ _ Heq) => /=.
  rewrite !(mulrC l) !divzMDr; try by apply/gtr_eqF/(ler_lt_trans x1).
  by rewrite !pdiv_small.
qed.

lemma divzMr i a b :  
  0 <= a => 0 <= b => i %/ (a * b) = i %/ a %/ b.
proof.
move=> ge0_a ge0_b.
case (a = 0) => [-> | neq0_a]; first by rewrite mul0r divz0 div0z.
case (b = 0) => [-> | neq0_b]; first by rewrite mulr0 2!divz0.
pose ab := a * b; move: (edivzP i ab) (divz_eq i a) (divz_eq (i %/ a) b) => [].
rewrite mulf_eq0 neq0_b neq0_a /= => eqi_ab rngi_ab eqi_a eqia_b.
move: (euclideU ab (i %/ ab) (i %/ a %/ b) (i %% ab) (i %/ a %% b * a + i %% a)).
move=> /(_ _ _ _) //; last rewrite andaE. 
+ by rewrite -eqi_ab /ab (mulrC a) mulrA addrA -mulrDl -eqia_b -eqi_a.
split; first by rewrite addz_ge0 1:mulr_ge0 1,3:modz_ge0.
rewrite ger0_norm 1:mulr_ge0 // (ltr_le_trans ((b - 1) * a + a)).
+ by rewrite ler_lt_add 1:ler_pmul 1:modz_ge0 // 1:-ltzS ltz_pmod ltr_def. 
by rewrite mulzDl mulNr -addzA addNz mulzC.
qed.

lemma divzMl i a b :
  0 <= a => 0 <= b => i %/ (a * b) = i %/ b %/ a.
proof. by move=> *; rewrite mulrC divzMr. qed.

(*
lemma modz_pow2_div n p i: 
  0 <= p <= n => (i %% 2^n) %/ 2^p = (i %/ 2^p) %% 2^(n-p).
proof.
move=> [ge0_p len_p].
rewrite !modzE (: 2^n = 2^(n-p) * 2^p) 1:-exprD_nneg 1:subr_ge0 3:subrK //.
by rewrite -mulNr mulrA divzMDr 1:expf_eq0 // mulNr addrC divzMl 1,2:expr_ge0.
qed.
*)

(* -------------------------------------------------------------------- *)
require import Real.

lemma fromint_div (x y : int) : y %| x => (x %/ y)%r = x%r / y%r.
proof.
case: (y = 0) => [->|nz_y] /=; first by rewrite divz0.
case/dvdzP => [q ->]; rewrite mulzK //.
by rewrite fromintM RField.mulrK // eq_fromint.
qed.
