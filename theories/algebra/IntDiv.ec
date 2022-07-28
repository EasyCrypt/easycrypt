(* -------------------------------------------------------------------- *)
require import Core Int IntMin Ring StdOrder List.
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

lemma nosmt pdiv_small n d: 0 <= n < d => n %/ d = 0.
proof. by move=> h; apply/divz_small => /#. qed.

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

lemma dvdz_div d m : d <> 0 => d %| m => m %/ d %| m.
proof. by move => neqd0 /dvdzP [q] ->; rewrite mulzK // dvdz_mulr dvdzz. qed.

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

lemma dvdNz d n : d %| n => -d %| n.
proof. by case/dvdzP => q ->>; apply/dvdzP; exists (-q); rewrite mulrNN. qed.

lemma dvdz_norml (d n : int) : `|d| %| n <=> d %| n.
proof.
case: (0 <= d) => [|/ltrNge] ?; [by rewrite ger0_norm|].
by rewrite ltr0_norm //; split => /dvdNz.
qed.

lemma dvdz_normr (d n : int) : d %| `|n| <=> d %| n.
proof.
case: (0 <= n) => [|/ltrNge] ?; [by rewrite ger0_norm|].
by rewrite ltr0_norm //; split => /dvdzN.
qed.

lemma dvdz_norm (d n : int) : `|d| %| `|n| <=> d %| n.
proof. by rewrite dvdz_norml dvdz_normr. qed.

lemma nosmt dvdzB d m1 m2 : d %| m1 => d %| m2 => d %| (m1 - m2).
proof. by move=> h1 h2; apply/dvdzD/dvdzN. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt dvdz_eq d m : (d %| m) <=> (m %/ d * d = m).
proof. by rewrite dvdzE modzE subr_eq0 eq_sym. qed.

lemma nosmt dvdz_exp2l p m n : 0 <= m <= n => (p ^ m %| p ^ n).
proof.
move=> [ge0_m le_mn]; rewrite dvdzE; rewrite -(subrK n m).
by rewrite exprD_nneg ?subr_ge0 // modzMl.
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

(* -------------------------------------------------------------------- *)
lemma divMr p q m : m %| q => (p * q) %/ m = p * (q %/ m).
proof.
case: (m = 0) => [-> /dvd0z ->|nz_m]; first by rewrite !div0z.
by case/dvdzP=> [k ->]; rewrite mulrA !mulzK.
qed.

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

lemma divz_eqP (m d n : int) :
  0 < d => m %/ d = n <=> n * d <= m < (n + 1) * d.
proof.
  move => lt0d; split => [<<-|[le_m ltm_]].
  + by split => [|_]; [apply/lez_floor/gtr_eqF|apply/ltz_ceil].
  by apply/eqz_leq; split; [apply/ltzS/ltz_divLR|apply/lez_divRL].
qed.

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

lemma eq_mod m n d : d %| (m - n) <=> m %% d = n %% d.
proof.
split => [/dvdzP [q] /subr_eq ->>|]; [by apply/modzMDl|].
move => eq_mod; apply/dvdzP; exists ((m - n) %/ d).
rewrite {1}(divz_eq (m - n) d) addrC eq_sym -subr_eq /= eq_sym.
by rewrite -modzDm eq_mod modzDm /= mod0z.
qed.

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

lemma nosmt expz_div (x n m : int) :
  0 <= m <= n => 0 < x => x^n %/ x^m = x^(n-m).
proof.
move=> [ge0_m le_mn] gt0_x; rewrite -{1}(subrK n m).
by rewrite exprD_nneg 1:subr_ge0 // mulzK // expf_eq0 (@gtr_eqF x).
qed.

(* -------------------------------------------------------------------- *)
lemma dvdz_divr d1 d2 n :
  d1 * d2 %| n =>
  d1 %| n %/ d2.
proof.
case (d2 = 0) => [->>/=|neq0]; [by rewrite divz0 dvdz0|].
by move => /dvdzP [q] ->>; rewrite mulrA mulzK // dvdz_mull dvdzz.
qed.

lemma dvdz_divl d1 d2 n :
  d1 * d2 %| n =>
  d2 %| n %/ d1.
proof. by rewrite mulrC; apply/ dvdz_divr. qed.

lemma divz_dvdr d1 d2 n :
  d1 <> 0 =>
  d1 %| d2 =>
  d2 %| n * d1 =>
  d2 %/ d1 %| n.
proof.
move => neq /dvdzP [q] ->>; rewrite mulzK // => /dvdzP [r].
by rewrite mulrA => eq_; apply/dvdzP; exists r; move: eq_; apply/mulIf.
qed.

lemma divz_dvdl d1 d2 n :
  d1 <> 0 =>
  d1 %| d2 =>
  d2 %| d1 * n =>
  d2 %/ d1 %| n.
proof. by rewrite mulrC; apply/divz_dvdr. qed.


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

lemma gcdnormz a b : gcd `|a| b = gcd a b.
proof. by rewrite /(`|_|); case (0 <= a) => //; rewrite gcdNz. qed.

lemma gcdznorm a b : gcd a `|b| = gcd a b.
proof. by rewrite gcdC gcdnormz gcdC. qed.

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

lemma coprime_dvdl a b c :
  coprime a b =>
  a %| b * c <=> a %| c.
proof.
move => coprime_a_b; split => [|]; [|by apply/dvdz_mull].
move => /dvdzP [q] eq_mul; case: (Bezout _ _ coprime_a_b) => u v eq_1.
by apply/dvdzP; exists (u * c + v * q); rewrite mulrDl -!mulrA -eq_mul !mulrA mulrAC -mulrDl eq_1.
qed.

lemma coprime_dvdr a b c :
  coprime a c =>
  a %| b * c <=> a %| b.
proof. by rewrite mulrC; apply/coprime_dvdl. qed.

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

lemma prime_or_2_odd p : prime p => p = 2 \/ odd p.
proof.
move => primep; case (p=2) => [->//|neqp2] /=.
move/ltzE/ler_eqVlt: (gt1_prime _ primep) => /=.
rewrite eq_sym neqp2 /= => /ltzE/lez_eqVlt.
case => [<<-|/ltzE /= lep4]; apply/oddP/negP => modp2.
+ by rewrite //= (modzMDl 1 1 2) modz_small in modp2.
move: primep; rewrite (divz_eq _ 2) modp2 /=.
apply/negP => -[_] /(_ 2); rewrite dvdz_mull ?dvdzz //=.
case: (normr_idP 2) => [_] -> //=; apply/ltr_eqF/ltz_divLR/ltzE => //.
by apply/lez_divRL => //=; rewrite divzz /b2i.
qed.

lemma nosmt prime_coprime p : prime p =>
  forall a, a %% p <> 0 => coprime p a.
proof.
move=> pm_p a nz_a; have h := dvdz_gcdl p a.
case: pm_p => gt1_p /(_ _ h) => {h}; rewrite ger0_norm ?ge0_gcd.
case=> // /eq_sym pE; have: p %| a  by rewrite {1}pE dvdz_gcdr.
by rewrite dvdzE nz_a.
qed.

lemma nosmt primeP p :
  prime p <=> (1 < p /\ forall a , a \in range 1 p => coprime p a).
proof.
split => [prime_p|]; [split|].
+ by apply/gt1_prime.
+ move => a mem_; apply/prime_coprime => //.
  rewrite modz_small ?gtr0_norm ?gt0_prime // -?mem_range.
  - by move: mem_; apply/mem_range_incl.
  by apply/gtr_eqF; move: mem_; apply/mem_range_lt.
move => [lt1p forall_]; split => // q dvdqp.
move: (dvdz_le _ _ _ dvdqp); [by rewrite gtr_eqF //; apply/(ler_lt_trans 1)|].
rewrite (gtr0_norm p) 1?(ler_lt_trans 1) // => /ler_eqVlt [<<-|lt_p] //=; left.
move/(_ `|q| _): forall_; [apply/mem_range; split => //|].
+ case/ler_eqVlt: (normr_ge0 q) => [/eq_sym/normr0P ->>|/ltzE] //.
  by move/dvd0z: dvdqp => ->>.
by move/dvdzP: dvdqp => [r] ->>; rewrite /coprime -gcdnormz normrM gcdC gcdMl normr_id.
qed.

lemma compositeP n :
  1 < n =>
  ! prime n =>
  exists a b , 1 < a /\ 1 < b /\ n = a * b.
proof.
move => lt1n; rewrite /prime; rewrite lt1n /= negb_forall /=.
case => a; rewrite negb_imply negb_or => -[dvdan] [neq_1 neq_n].
exists `|a| (n %/ `|a|); rewrite mulrC divzE modz_abs !ltrNge.
move/dvdzE: (dvdan) => -> /=; rewrite -negb_or !ler_norml.
rewrite !le2_mem_range /= 3?range_ltn //= range_geq //=.
apply/negP; case => [[|[|]] ->> //=|]; [by move/dvd0z: dvdan => ->>|].
rewrite lez_divLR ?dvdzE ?modz_abs -?dvdzE //= ?ltrNge.
+ apply/negP => le_0; move: (eqz_leq 0 `|a|); rewrite le_0 normr_ge0 /=.
  by rewrite eq_sym normr0P; apply/negP => ->>; move/dvd0z: dvdan => ->>.
move: (dvdz_le _ _ _ dvdan); [by apply/gtr_eqF/ltzE/ltzW|].
rewrite (ger0_norm n); [by apply/ltzW/ltzE/ltzW|move => ?; apply/negP => ?].
by move: neq_n; rewrite eqz_leq /=; split.
qed.

lemma prime2 :
  prime 2.
proof. by apply/primeP => /=; rewrite range_ltn // range_geq. qed.

lemma dvd_prime p a :
  prime p =>
  0 <= a =>
  a %| p =>
  a = 1 \/ a = p.
proof. by move => prime_p le0a dvdap; case: prime_p => _ /(_ a _) //; rewrite ger0_norm. qed.

lemma gcd_prime p a :
  prime p =>
  gcd p a = 1 \/ gcd p a = p.
proof. by move => prime_p; move: (dvdz_gcdl p a); apply/dvd_prime. qed.

lemma dvd_prime_mul p a b :
  prime p =>
  p %| a * b <=> p %| a \/ p %| b.
proof.
move => prime_p; split; [|by case; [apply/dvdz_mulr|apply/dvdz_mull]].
case: (gcd_prime _ a prime_p) => eq_gcd; [|by move: (dvdz_gcdr p a); rewrite eq_gcd => ->].
by move => dvdp; move: (coprime_dvdl p a b); rewrite /coprime eq_gcd dvdp /= => ->.
qed.

lemma prime_mul a b :
  0 < a =>
  0 < b =>
  prime (a * b) <=>
  ((prime a /\ b = 1) \/ (a = 1 /\ prime b)).
proof.
move => lt0a lt0b; split; [|by case => [[prime_a ->>]|[->> prime_b]]].
move => [lt1_ hforall]; case: (hforall a _); [by apply/dvdz_mulr/dvdzz| |].
+ by rewrite gtr0_norm // => ->> /=; right; split.
rewrite gtr0_norm // mulrC eqz_mul ?dvdzz //; [by apply/gtr_eqF|].
rewrite divzz (gtr_eqF a) // /b2i /= => <<- /=; left.
by rewrite /= in lt1_; rewrite /= in hforall; split.
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
require import List.

op is_pd n p = prime p /\ p %| n.

lemma is_pd_prime n p :
  is_pd n p =>
  prime p.
proof. by case. qed.

lemma is_pd_1 p :
  !is_pd 1 p.
proof.
rewrite /is_pd negb_and; case: (prime p) => //= /gt1_prime lt1p.
by rewrite dvdz1 eqr_norml /= negb_or; split; apply/gtr_eqF => //; apply/(ltr_trans 1).
qed.

lemma is_pd_p p :
  prime p =>
  is_pd p p.
proof. by move => ?; split => //; rewrite dvdzz. qed.

lemma is_pd_dvd m n p :
  m %| n =>
  is_pd m p =>
  is_pd n p.
proof. by move => ? [??]; split => //; apply/(dvdz_trans m). qed.

lemma is_pd_mulr m n p :
  is_pd m p =>
  is_pd (m * n) p.
proof. by move => [? ?]; split => //; rewrite dvdz_mulr. qed.

lemma is_pd_mull m n p :
  is_pd n p =>
  is_pd (m * n) p.
proof. by rewrite mulrC; apply/is_pd_mulr. qed.

lemma prime_divisor n :
  1 < n =>
  exists p , is_pd n p.
proof.
move => lt1n; move: (ler_trans _ 0 _ _ (ltzW _ _ lt1n)) {1 2 4}n (lt1n) (lerr n) => // {lt1n}.
elim: n => [|n le0n IHn] k lt1k lekn; [by move: (ltr_le_trans _ _ _ lt1k lekn)|].
case/ler_eqVlt: lekn => [->>|/ltzS]; [|by apply/IHn].
case: (prime (n + 1)) => [prime_p|]; [by exists (n + 1); split => //; apply/dvdzz|].
rewrite /prime negb_and lt1k /= negb_forall => -[d] /=; rewrite negb_imply negb_or.
move => [dvd_d] [neq_1 neq_]; case: (IHn `|d| _ _) => [ | |p].
+ case/ler_eqVlt: (normr_ge0 d).
  - by rewrite eq_sym normr0P => ->>; move: dvd_d lt1k; rewrite dvd0z => ->.
  by case/ltzE/ler_eqVlt => //=; rewrite eq_sym neq_1.
+ apply/ltzS; move: (dvdz_le _ _ _ dvd_d); [by apply/gtr_eqF/ltzE/ltzW|].
  by rewrite (ger0_norm (n + 1)); [apply/ltzW/ltzE/ltzW|case/ler_eqVlt].
move => is_pd_p; exists p; apply/(is_pd_dvd `|d|) => //; move: dvd_d.
rewrite /CoreInt.absz; case: (0 <= d) => // _ dvd_d; apply/(dvdz_trans d) => //.
by rewrite -{2}opprK dvdzN dvdzz.
qed.

(* -------------------------------------------------------------------- *)
op is_pds n = all (is_pd n).

lemma is_pds_primes n ps :
  is_pds n ps =>
  all prime ps.
proof. by apply/all_imp_in/allP => ? _ /=; apply/is_pd_prime. qed.

lemma is_pds_nil n :
  is_pds n [].
proof. by []. qed.

lemma is_pds_cons n p ps :
  is_pds n (p :: ps) <=> (is_pd n p /\ is_pds n ps).
proof. by rewrite /is_pds. qed.

lemma is_pds_cat n ps1 ps2 :
  is_pds n (ps1 ++ ps2) <=> (is_pds n ps1 /\ is_pds n ps2).
proof. by elim: ps1 => // p ps1 /=; rewrite !is_pds_cons => ->; rewrite andbA. qed.

lemma is_pds_catC n ps1 ps2 :
  is_pds n (ps1 ++ ps2) <=> is_pds n (ps2 ++ ps1).
proof. by rewrite !is_pds_cat andbC. qed.

lemma is_pds_perm n ps1 ps2 :
  perm_eq ps1 ps2 =>
  is_pds n ps1 <=> is_pds n ps2.
proof. by move => /perm_eq_mem eq_; rewrite /is_pds !allP; apply/forall_eq => ? /=; rewrite eq_. qed.

lemma is_pds_mulr m n ps :
  is_pds m ps =>
  is_pds (m * n) ps.
proof. by apply/all_imp_in/allP => ? _ /=; apply/is_pd_mulr. qed.

lemma is_pds_mull m n ps :
  is_pds n ps =>
  is_pds (m * n) ps.
proof. by rewrite mulrC; apply/is_pds_mulr. qed.

lemma is_pds_nseq n p k :
  is_pd n p =>
  is_pds n (nseq k p).
proof. by move => ?; rewrite /is_pds all_nseq; right. qed.

(* -------------------------------------------------------------------- *)
lemma sumz_nil :
  sumz [] = 0.
proof. by []. qed.

lemma sumz_cons z sz :
  sumz (z :: sz) = z + sumz sz.
proof. by []. qed.

lemma sumz_cat sz1 sz2 :
  sumz (sz1 ++ sz2) = sumz sz1 + sumz sz2.
proof. by elim: sz1 => // z sz1 /=; rewrite !sumz_cons => ->; rewrite addrA. qed.

lemma sumz_flatten ssz :
  sumz (flatten ssz) = sumz (map sumz ssz).
proof.
elim: ssz => [|sz ssz IHssz]; [by rewrite flatten_nil|].
by rewrite flatten_cons sumz_cat /= sumz_cons IHssz.
qed.

lemma sumz_catC sz1 sz2 :
  sumz (sz1 ++ sz2) = sumz (sz2 ++ sz1).
proof. by rewrite !sumz_cat addrC. qed.

lemma sumz_perm sz1 sz2 :
  perm_eq sz1 sz2 =>
  sumz sz1 = sumz sz2.
proof. by apply/(foldr_perm ( + ) 0)/addrCA. qed.

lemma sumz_nseq m n :
  sumz (nseq m n) = if 0 <= m then m * n else 0.
proof.
case (0 <= m) => [|/ltrNge/ltzW ltm0]; [|by rewrite nseq0_le].
elim: m => [|m le0m IHm]; [by rewrite nseq0 mul0r|].
by rewrite nseqS // sumz_cons IHm mulrDl /= addrC.
qed.

lemma sumz_filter0 sz :
  sumz sz = sumz (filter (predC1 0) sz).
proof.
elim: sz => // z sz IHsz; rewrite sumz_cons /= {1}/predC1.
by case (z = 0) => [->>|_] //=; rewrite sumz_cons IHsz.
qed.

(* -------------------------------------------------------------------- *)
op mulz sz = foldr ( * ) 1 sz.

lemma mulz_nil :
  mulz [] = 1.
proof. by []. qed.

lemma mulz_cons z sz :
  mulz (z :: sz) = z * mulz sz.
proof. by []. qed.

lemma mulz_cat sz1 sz2 :
  mulz (sz1 ++ sz2) = mulz sz1 * mulz sz2.
proof. by elim: sz1 => // z sz1 /=; rewrite !mulz_cons => ->; rewrite mulrA. qed.

lemma mulz_flatten ssz :
  mulz (flatten ssz) = mulz (map mulz ssz).
proof.
elim: ssz => [|sz ssz IHssz]; [by rewrite flatten_nil|].
by rewrite flatten_cons mulz_cat /= mulz_cons IHssz.
qed.

lemma mulz_catC sz1 sz2 :
  mulz (sz1 ++ sz2) = mulz (sz2 ++ sz1).
proof. by rewrite !mulz_cat mulrC. qed.

lemma mulz_perm sz1 sz2 :
  perm_eq sz1 sz2 =>
  mulz sz1 = mulz sz2.
proof. by apply/(foldr_perm ( * ) 1)/mulrCA. qed.

lemma mulz_nseq m n :
  mulz (nseq m n) = if 0 <= m then n ^ m else 1.
proof.
case (0 <= m) => [|/ltrNge/ltzW ltm0]; [|by rewrite nseq0_le].
elim: m => [|m le0m IHm]; [by rewrite nseq0 expr0|].
by rewrite nseqS // mulz_cons exprS // IHm.
qed.

lemma mulz_filter1 sz :
  mulz sz = mulz (filter (predC1 1) sz).
proof.
elim: sz => // z sz IHsz; rewrite mulz_cons /= {1}/predC1.
by case (z = 1) => [->>|_] //=; rewrite mulz_cons IHsz.
qed.

(* -------------------------------------------------------------------- *)
lemma primes_is_pds_mulz ps :
  all prime ps =>
  is_pds (mulz ps) ps.
proof.
elim: ps => // p ps IHps /= [?] /IHps; rewrite is_pds_cons mulz_cons /= => is_pds_ps; split.
+ by apply/is_pd_mulr/is_pd_p.
by apply/is_pds_mull.
qed.

(* -------------------------------------------------------------------- *)
op is_pdec n ps = is_pds n ps /\ n = mulz ps.

lemma is_pdec_1 n ps :
  is_pdec n ps =>
  n = 1 <=> ps = [].
proof.
rewrite /is_pdec /is_pds; move => [all_ ->>]; split => // eq_1; move: eq_1 all_ => ->.
by elim: ps => // p ps _ /=; rewrite is_pd_1.
qed.

lemma is_pdec_nil n :
  is_pdec n [] <=>
  n = 1.
proof. by rewrite /is_pdec; split => [[]|]. qed.

lemma is_pdec_cons n p ps :
  is_pdec n (p :: ps) <=>
  (is_pd n p /\ is_pdec (n %/ p) ps).
proof.
rewrite /is_pdec is_pds_cons mulz_cons -andbA; apply/andb_id2l => is_pd_p.
rewrite eqboolP; split => [[is_pds_ps ->>]|[is_pds_ps eq_]].
+ rewrite mulrC mulzK /=; [by apply/gtr_eqF/gt0_prime; move: is_pd_p; apply/is_pd_prime|].
  move: is_pds_ps; apply/all_imp_in/allP => x mem_ /= [? ?]; split => //.
  by rewrite (mulz_perm _ (x :: rem x ps)) ?mulz_cons ?dvdz_mulr; [apply/perm_to_rem|apply/dvdzz].
rewrite mulrC -eq_ divzK /=; [by case: is_pd_p|]; rewrite -(divzK p n); [by case: is_pd_p|].
by move: is_pds_ps; apply/all_imp_in/allP => x _ /= [? ?]; split => //; rewrite dvdz_mulr.
qed.

lemma is_pdec_cat n ps1 ps2 :
  is_pdec n (ps1 ++ ps2) <=>
  (exists n1 n2 , is_pdec n1 ps1 /\ is_pdec n2 ps2 /\ n = n1 * n2).
proof.
rewrite /is_pdec is_pds_cat mulz_cat; split => [[] [is_pds1 is_pds2] ->>|[n1 n2] [] [is_pds1 ->>] [] [is_pds2 ->>] ->>].
+ exists (mulz ps1) (mulz ps2); rewrite !primes_is_pds_mulz //.
  - by move: is_pds1; apply/is_pds_primes.
  by move: is_pds2; apply/is_pds_primes.
by rewrite is_pds_mulr // is_pds_mull.
qed.

lemma prime_divisors n :
  0 < n =>
  exists ps , is_pdec n ps.
proof.
move => lt0n; move: (ltzW _ _ lt0n) {1 2 4}(n) (lt0n) (lerr n) => {lt0n}.
elim: n => [|n le0n IHn] m lt0m lemn; [by move: (ltr_le_trans _ _ _ lt0m lemn)|].
case/ler_eqVlt: lemn => [->> {lt0m}|/ltzS]; [|by apply/IHn].
case/ler_eqVlt: le0n => [<<-|lt0n]; [by exists []; rewrite /is_pds|].
case: (prime_divisor (n + 1) _) => [|p is_pd_p]; [by rewrite -ltr_subl_addr|].
case: (IHn ((n + 1) %/ p) _ _).
+ by case: is_pd_p => prime_p dvd_p; apply/ltz_divRL => //=; [apply/gt0_prime|apply/ltzS/ltzW].
+ case: is_pd_p => prime_p dvd_p; apply/ltzS/ltz_divLR; [by apply/gt0_prime|].
  rewrite -subr_gt0 -{2}(mul1r (n + 1)) -mulNr mulrC -mulrDl.
  by rewrite mulr_gt0; [apply/subr_gt0/gt1_prime|apply/ltzS/ltzW].
by move => ps is_pdec_ps; exists (p :: ps); rewrite is_pdec_cons; split.
qed.

lemma perm_eq_prime_divisors n ps1 ps2 :
  perm_eq ps1 ps2 =>
  is_pdec n ps1 =>
  is_pdec n ps2.
proof. by move => eq_; rewrite /is_pdec; apply/andb_id2; [by apply/is_pds_perm/perm_eq_sym|rewrite (mulz_perm _ _ eq_)]. qed.

lemma is_pdec_ps n p ps :
  is_pdec n ps =>
  is_pd n p <=> p \in ps.
proof.
elim: ps n => [|q ps IHps] n; [by rewrite is_pdec_nil => ->>; rewrite is_pd_1|].
rewrite is_pdec_cons => -[[prime_q dvd_q] is_pdec_ps]; move: IHps => /(_ (n %/ q) _) => //= <-.
split => [[prime_p dvd_p]|[<<-|[prime_p dvd_p]]]; [|by split|]; last first.
+ by split => //; apply/(dvdz_trans (n %/ q)) => //; apply/dvdz_div => //; apply/gtr_eqF/gt0_prime.
case (p = q) => [<<-|] //= neqpq; split => //; move: dvd_p dvd_q.
case/dvdzP => m ->>; case/(dvd_prime_mul _ _ _ prime_q) => /dvdzP [l] ->>.
+ by rewrite mulrAC mulzK; [apply/gtr_eqF/gt0_prime|apply/dvdz_mull => //; apply/dvdzz].
have ->>//: l = 1; move: (gt0_prime _ prime_q) (gt0_prime _ prime_p).
move => lt0q; rewrite pmulr_lgt0 // => lt0l; move: prime_p.
rewrite prime_mul //; case => [[_ ->>]|]; [by move/gt1_prime: prime_q|].
by move => [->>].
qed.

lemma prime_divisors_perm_eq n ps1 ps2 :
  0 < n =>
  is_pdec n ps1 =>
  is_pdec n ps2 =>
  perm_eq ps1 ps2.
proof.
elim: ps1 ps2 n => [|p1 ps1 IHps1] ps2 n lt0n //=; rewrite ?is_pdec_nil ?is_pdec_cons.
+ by move => ->> /is_pdec_1 /= ->.
move => [is_pd_p is_pdec_ps1] is_pdec_ps2; move: (IHps1 (rem p1 ps2) (n %/ p1) _ _ _) => //.
+ by move: is_pd_p => [/gt0_prime lt0p1 dvd_p]; apply/ltz_divRL.
+ move: (IHps1 (rem p1 ps2) (n %/ p1) _ _ _) => //.
  - case: is_pd_p => prime_p dvd_p; apply/ltzE/lez_divRL; [by apply/gt0_prime|].
    move: (dvdz_le _ _ _ dvd_p); [by apply/gtr_eqF|].
    by rewrite !gtr0_norm // ?gt0_prime //.
  - move/(is_pdec_ps _ _ _ is_pdec_ps2): {is_pdec_ps1} (is_pd_p) => mem_p1.
    move: (perm_eq_prime_divisors _ _ _ (perm_to_rem _ _ mem_p1) is_pdec_ps2).
    by rewrite is_pdec_cons; case.
  by move => perm_eq_; move: perm_eq_ is_pdec_ps1; apply/perm_eq_prime_divisors.
rewrite -(perm_cons p1) => perm_eq_; apply/(perm_eq_trans _ _ _ perm_eq_) => {perm_eq_}.
by apply/perm_eq_sym/perm_to_rem/(is_pdec_ps _ _ _ is_pdec_ps2).
qed.

lemma is_pdec_nseq p n :
  prime p =>
  0 < n =>
  is_pdec (p ^ n) (nseq n p).
proof.
move => ? lt0n; rewrite /is_pdec mulz_nseq ltzW //= is_pds_nseq //.
by split => //; rewrite -{1}expr1; apply/dvdz_exp2l => /=; move/ltzE: lt0n.
qed.

lemma is_pdec_dvd d n psd psn :
  is_pdec d psd =>
  is_pdec n psn =>
  d %| n <=> true.
proof.
fail.
qed.

(* -------------------------------------------------------------------- *)
op is_ppdec n pps =
  uniq (unzip1 pps) /\
  all (fun (p : int * int) => 0 < p.`2) pps /\
  is_pdec n (flatten (map (fun (p : int * int) => nseq p.`2 p.`1) pps)).

lemma is_ppdec_uniq n pps :
  is_ppdec n pps =>
  uniq pps.
proof. by case => |> + _ _; apply/uniq_map. qed.

lemma is_ppdec_1 n pps :
  is_ppdec n pps =>
  n = 1 <=> pps = [].
proof.
move => [_ [all_gt0 /is_pdec_1 ->]]; split => [|->>]; [|by rewrite flatten_nil].
case: pps all_gt0 => // -[p k] pps /= [lt0k _]; rewrite flatten_cons -size_eq0.
by rewrite size_cat size_nseq gtr_eqF // ler_maxr 1:ltzW // ltr_paddr.
qed.

lemma is_ppdec_nil n :
  is_ppdec n [] <=>
  n = 1.
proof. by split => [/is_ppdec_1|->>]. qed.

lemma is_ppdec_cons n p k pps :
  is_ppdec n ((p, k) :: pps) <=>
  (is_pd n p /\ 0 < k /\ p ^ k %| n /\ ! p %| n %/ (p ^ k) /\ is_ppdec (n %/ (p ^ k)) pps).
proof.
rewrite /is_ppdec /= flatten_cons is_pdec_cat; split.
+ move => |> Nmem_ uniq_ lt0k all_ n1 n2 [is_pds_ ->>] is_pdec2.
  rewrite mulz_nseq ltzW //= dvdz_mulr ?dvdzz //=; move: is_pds_.
  rewrite -{2}(subrK k 1) nseqS -?ltzS // => /is_pds_cons [[prime_p _] _].
  rewrite mulKz ?gtr_eqF ?expr_gt0 ?gt0_prime //= is_pdec2 /=; split; last first.
  - move: (is_pdec_ps _ p _ is_pdec2); rewrite -flattenP -iff_negb negb_exists /=.
    rewrite /is_pd prime_p /= => -> ps; rewrite negb_and -implybE.
    move => /mapP [] [q l] [mem_ ->>] /=; rewrite mem_nseq.
    move/allP/(_ (q, l) _): all_ => //= -> /=; move: Nmem_; apply/contra => ->>.
    by apply/mapP; exists (p, l).
  by split => //; apply/dvdz_mulr; rewrite -{1}expr1; apply/dvdz_exp2l => /=; move/ltzE: lt0k.
move => |> is_pd_ lt0k dvd_n Ndvdp_ uniq_ all_ is_pdec_; split.
+ apply/negP => /mapP [] [? l] [mem_ /=]; apply/negP => <<-.
  move/allP/(_ (p, l) _): all_ => //=; apply/negP => lt1l.
  move/(is_pdec_ps _ p): is_pdec_; rewrite -flatten_mapP.
  rewrite /is_pd (is_pd_prime _ _ is_pd_) Ndvdp_ /=.
  by exists (p, l); rewrite mem_nseq /=.
exists (p ^ k) (n %/ p ^ k); rewrite is_pdec_ /= is_pdec_nseq //=; [by move: is_pd_; apply/is_pd_prime|].
by rewrite mulrC divzK.
qed.

lemma pow_prime_divisors n :
  0 < n =>
  exists pps , is_ppdec n pps.
proof.
case/prime_divisors => ps is_pdec_.
exists (map (fun p => (p, count (pred1 p) ps)) (undup ps)).
rewrite /is_ppdec; do!split.
+ rewrite -map_comp (eq_map _ idfun).
  - by move => ?; rewrite /(\o) /idfun.
  by rewrite map_id undup_uniq.
+ apply/allP => -[p k] /mapP [?] []; rewrite mem_undup.
  by move => mem_ /= [<<- ->>]; apply/has_count/hasP; exists p.
+ apply/allP => p /flatten_mapP [] [? k] /= []; rewrite mem_nseq => + [lt0k ->>].
  move => /mapP [?] /= [] + [<<- ->>]; rewrite mem_undup => mem_.
  by rewrite (is_pdec_ps _ _ _ is_pdec_).
case: is_pdec_ => _ ->>; apply/mulz_perm/perm_eqP1 => p.
rewrite count_flatten -!map_comp; pose f:= (_ \o _).
case: (eq_in_map f (fun q => if p = q then count (pred1 p) ps else 0) (undup ps)) => [+ _].
move => ->; rewrite /f => {f}; [|rewrite sumz_filter0].
+ move => q mem_; rewrite /(\o) /=; rewrite -filter_pred1 count_filter.
  case (p = q) => [<<-|neqpq]; [by apply/eq_count => ?; rewrite /predI /pred1|].
  by apply/count_pred0_eq => ?; rewrite /predI /pred1 negb_and; apply/implybE => ->>.
case: (p \in ps) => [mem_|Nmem_]; [move: (mem_) (undup_uniq ps)|].
+ rewrite -mem_undup => /splitPr [ps1 ps2] eq_; rewrite eq_ map_cat /=.
  rewrite cat_uniq /= => |>; rewrite !negb_or => |> _ Nmem1 _ Nmem2 _.
  rewrite -cat1s !filter_cat !sumz_cat filter_cons /=.
  rewrite eq_in_filter_pred0; [by move => ? /mapP [q] /= [+ ->>]; rewrite /predC1 => memq; case (p = q)|].
  rewrite eq_in_filter_pred0; [by move => ? /mapP [q] /= [+ ->>]; rewrite /predC1 => memq; case (p = q)|].
  by rewrite sumz_nil /predC1 /=; move/ler_eqVlt: (count_ge0 (pred1 p) ps) => [<-|lt0_] //=; rewrite (gtr_eqF _ 0).
rewrite eq_in_filter_pred0; [by move => ? /mapP [q] /= [+ ->>]; rewrite mem_undup /predC1 => mem_; case (p = q)|].
by rewrite count_pred0_eq_in; [move => ? ?; rewrite /pred1; apply/negP => ->>|rewrite sumz_nil].
qed.

lemma perm_eq_pow_prime_divisors n pps1 pps2 :
  perm_eq pps1 pps2 =>
  is_ppdec n pps1 =>
  is_ppdec n pps2.
proof.
rewrite /is_ppdec => |> eq_ uniq_ all_ is_pdec_; split; [|split].
+ by rewrite -(perm_eq_uniq (unzip1 pps1)) //; apply/perm_eq_map.
+ apply/allP => -[p k] mem_ /=; move/allP/(_ (p, k) _): all_ => //.
  by rewrite (perm_eq_mem _ _ eq_).
by move: is_pdec_; apply/perm_eq_prime_divisors; apply/perm_eq_flatten/perm_eq_map.
qed.

lemma is_ppdec_pps n p pps :
  is_ppdec n pps =>
  is_pd n p <=> p \in unzip1 pps.
proof.
case => _ [all_] /is_pdec_ps ->; rewrite -flatten_mapP mapP /=.
rewrite -iff_negb !negb_exists /=; apply/forall_eq => -[q k] /=.
rewrite eqboolP iff_negb; apply/andb_id2l => mem_; move/allP/(_ (q, k) _): all_ => //=.
by rewrite mem_nseq => ->; rewrite /= (eq_sym p).
qed.

lemma is_ppdec_mem n p k pps :
  is_ppdec n pps =>
  (prime p /\ 0 < k /\ p ^ k %| n /\ ! p %| n %/ p ^ k) <=> (p, k) \in pps.
proof.
move => is_ppdec; split => |>; last first.
+ by move => /perm_to_rem eq_; move/is_ppdec_cons: (perm_eq_pow_prime_divisors _ _ _ eq_ is_ppdec) => |> [].
move => prime_p lt0k dvdkn Ndvdk; move: (is_ppdec_pps _ p _ is_ppdec); rewrite /is_pd prime_p (dvdz_trans (p ^ k)) //=.
+ by rewrite -{1}expr1 dvdz_exp2l /=; move/ltzE: lt0k.
move => /mapP [] [? l] [+ /= <<-]; move => mem_; move/perm_to_rem: (mem_) => eq_.
move/is_ppdec_cons: (perm_eq_pow_prime_divisors _ _ _ eq_ is_ppdec) => |> _ lt0l dvdln Ndvdl _.
case: (eqz_leq k l) => _ /(_ _); [|by move => /= <<-]; split; rewrite lerNgt; apply/negP => [ltlk|ltkl].
+ apply/Ndvdl/dvdz_divr; rewrite -exprS ?ltzW //; apply/(dvdz_trans _ _ _ _ dvdkn).
  by apply/dvdz_exp2l; rewrite addr_ge0 1:ltzW // -ltzE.
apply/Ndvdk/dvdz_divr; rewrite -exprS ?ltzW //; apply/(dvdz_trans _ _ _ _ dvdln).
by apply/dvdz_exp2l; rewrite addr_ge0 1:ltzW // -ltzE.
qed.

lemma pow_prime_divisors_perm_eq n pps1 pps2 :
  0 < n =>
  is_ppdec n pps1 =>
  is_ppdec n pps2 =>
  perm_eq pps1 pps2.
proof.
move => lt0n is_ppdec1 is_ppdec2; apply/uniq_perm_eq.
+ by move: is_ppdec1; apply/is_ppdec_uniq.
+ by move: is_ppdec2; apply/is_ppdec_uniq.
by move => [p k]; rewrite -(is_ppdec_mem _ _ _ _ is_ppdec1) -(is_ppdec_mem _ _ _ _ is_ppdec2).
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

lemma nosmt divzMr i a b :  
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

lemma nosmt divzMl i a b :
  0 <= a => 0 <= b => i %/ (a * b) = i %/ b %/ a.
proof. by move=> *; rewrite mulrC divzMr. qed.

(*
lemma nosmt modz_pow2_div n p i: 
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
