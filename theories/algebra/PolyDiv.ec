(* -------------------------------------------------------------------- *)
require import AllCore Finite Distr DList List.
require import Poly Ring IntMin Bigalg StdBigop StdOrder.
(*---*) import Bigint IntID IntOrder.

abstract theory RingPseudoDivision.

type coeff, poly.

clone ComRing as CR with type t <= coeff.

clone PolyComRing as PCR with
  type   coeff <= coeff,
  type   poly  <= poly,
  theory Coeff <- CR.

(*TODO: Bad clone, duplicates stuff, should import instead*)
clone RingPseudoDivision.PCR.PolyComRing as PS.
(*Example:*)
(*
lemma foo x n :
  PS.exp x n = RingPseudoDivision.PCR.PolyComRing.exp x n.
proof. by trivial. qed.
*)

import CR.
import PCR.

(* It will go through useless loops once "deg r < sq" since iter is needed
   as recursive calls are currently not allowed. *)
op redivp_rec_it (i :  int * poly * poly * poly * int * coeff) =
  let (k, qq, r, q, sq, cq) = i in
  if deg r < sq then i else
  let m = (lc r) ** polyXn (deg r - sq) in
  let qq1 = qq * polyC cq + m in
  let r1 = r * polyC cq - m * q in
  (k + 1, qq1, r1, q, sq, cq).

(* Is a condition needed? *)
op redivp_rec (k : int) (qq r : poly) (n : int) (q : poly) =
  let sq = deg q in
  let cq = lc q in
  let i = iter n redivp_rec_it (k, qq, r, q, sq, cq) in
  let (k1, qq1, r1, q1, sq1, cq1) = i in
  (k1, qq1, r1).

op redivp (p q : poly) =
  if q = poly0 then (0, poly0, p) else redivp_rec 0 poly0 p (deg p) q.

op rdivp p q = let (scal, div, mod) = redivp p q in div.
op rmodp p q = let (scal, div, mod) = redivp p q in mod.
op rscalp p q = let (scal, div, mod) = redivp p q in scal.
op rdvdp p q = (rmodp q p = poly0).

lemma redivp_def p q : redivp p q = (rscalp p q, rdivp p q, rmodp p q) by smt().

lemma redivp_recS k qq r n q :
  0 <= n =>
  redivp_rec k qq r (n + 1) q =
  let (k1, qq1, r1) = redivp_rec k qq r n q in
  let (k2, qq2, r2, q2, sq, cq) = redivp_rec_it (k1, qq1, r1, q, deg q, lc q) in
  (k2, qq2, r2).
proof.
move => n_ge0; rewrite {1}/redivp_rec /= iterS //.
suff /# : iter n redivp_rec_it (k, qq, r, q, deg q, lc q) =
          let (k1, qq1, r1) = redivp_rec k qq r n q in
          (k1, qq1, r1, q, deg q, lc q).
by rewrite /redivp_rec /=; move: n n_ge0; apply intind; smt(iterS iter0).
qed.

lemma redivp_recSr k qq r n q :
  0 <= n =>
  redivp_rec k qq r (n + 1) q =
  let (k1, qq1, r1, q1, sq1, cq1) = redivp_rec_it (k, qq, r, q, deg q, lc q) in
  redivp_rec k1 qq1 r1 n q
  by move => n_ge0; rewrite {1}/redivp_rec /= iterSr /#.

lemma rdiv0p p : rdivp poly0 p = poly0 by smt(deg0 iter0).

lemma rdivp0 p : rdivp p poly0 = poly0 by smt().

lemma iter_id ['a] n opr (x : 'a) : opr x = x => iter n opr x = x.
proof.
case: (0 <= n); 2: by smt(iter0).
move: n; apply intind; 1: by smt(iter0).
by move => /= n n_ge0 nh xP; rewrite iterS // nh.
qed.

lemma rdivp_small p q : deg p < deg q => rdivp p q = poly0.
proof.
rewrite /rdivp /redivp /redivp_rec /=; case: (q = poly0) => //= q_neq0.
by move => degP; rewrite iter_id //= /redivp_rec_it /= degP.
qed.

lemma degXn i : 0 <= i => deg (polyXn i) = i + 1
  by move => ge0_i; apply: degP; smt(coeffE oner_neq0 ispolyXn).

lemma lcXn i : 0 <= i => lc (polyXn i) = oner
  by smt(coeffE degXn ispolyXn).

lemma coeff_polyXn i j :
  0 <= i => (polyXn i).[j] = if i = j then oner else zeror
  by smt(coeffE ispolyXn).

lemma polyXn0 : polyXn 0 = poly1 by smt(coeff_polyXn polyCE poly_eqP).

(* PolyComRing.mulrC used! *)
lemma leq_rdivp p q : deg (rdivp p q) <= deg p.
proof.
case: (deg p < deg q); 1: by smt(deg0 ge0_deg rdivp_small).
pose n := deg p; move => degP; have {degP} : deg q <= n by smt().
case: (q = poly0) => q_neq0; 1: by smt(deg0 ge0_deg rdivp0).
have [] : 0 <= n /\ deg p <= n by smt(ge0_deg).
rewrite /rdivp /redivp q_neq0 /=.
suff /# : forall k, 0 <= k => k <= n => deg q <= n =>
                    deg (let (s, d, r) = redivp_rec 0 poly0 p k q in d) <= n /\
                    deg (let (s, d, r) = redivp_rec 0 poly0 p k q in r) <= n.
apply intind; 1: by rewrite /redivp_rec /= iter0 //= deg0.
move => k k_ge0 /= kh knP nqP; rewrite redivp_recS //.
pose qq1 := let (s, d, r) = redivp_rec 0 poly0 p k q in d.
pose r1  := let (s, d, r) = redivp_rec 0 poly0 p k q in r.
rewrite /redivp_rec_it; case: (deg r1 < deg q) => [/#|r1qP].
have qqP : qq1 * polyC (lc q) = lc q ** qq1 by rewrite scalepE PS.mulrC.
have rP : r1 * polyC (lc q) = lc q ** r1 by rewrite scalepE PS.mulrC.
pose m := polyXn (deg r1 - deg q); suff: deg m <= n /\ deg (m * q) <= n
  by smt(degB degD degZ_le PS.mulrA scalepE).
suff: deg (m * q) <= n by smt(mul1r degM_proper deg_gt0 lcXn lc_eq0).
by rewrite degM_proper; smt(mul1r degXn lcXn lc_eq0).
qed.

lemma rmod0p p : rmodp poly0 p = poly0 by smt(deg0 iter0).

lemma rmodp0 p : rmodp p poly0 = p by smt().

lemma rscalp_small p q : deg p < deg q => rscalp p q = 0.
proof.
rewrite /rscalp /redivp /redivp_rec /=; case: (q = poly0) => //= q_neq0.
by move => degP; rewrite iter_id //= /redivp_rec_it /= degP.
qed.

lemma rscalp_ge0 p q : 0 <= rscalp p q.
proof.
rewrite /rscalp /redivp /redivp_rec; case: (q = poly0) => [/#|q_neq0].
suff /# : forall n k i i', i' = iter n redivp_rec_it i =>
                           k <= i.`1 => k <= i'.`1.
by apply: natind => [|n n_ge0 /= nh k i i']; smt(iter0 iterSr).
qed.

(* PolyComRing.mulrC used! *)
lemma ltn_rmodp p q : (deg (rmodp p q) < deg q) = (q <> poly0).
proof.
rewrite /rmodp /redivp; case: (q = poly0) => q_neq0; 1: by smt(deg0 ge0_deg).
have: 0 <= deg p by smt(ge0_deg).
suff /# : forall n, 0 <= n => forall k qq r, deg r <= n =>
                    deg ((redivp_rec k qq r n q).`3) < deg q.
apply intind; 1: by smt(deg_gt0 iter0).
move => n n_ge0 /= kh {p} k qq r krP.
case: (deg r < deg q); 1: by smt(iter_id).
rewrite redivp_recSr // => degqrP.
suff /# : deg (redivp_rec_it (k, qq, r, q, deg q, lc q)).`3 <= n.
rewrite /redivp_rec_it /= degqrP /=; apply: deg_leP => // i iP.
rewrite polyDE polyNE PS.mulrC scalepE -PS.mulrA -!scalepE.
rewrite !polyZE polyME (BigCf.BCA.big_rem _ _ _ (deg r - deg q)) /predT /=;
  1: by smt(deg_gt0 mem_range).
rewrite coeff_polyXn /= ?mul1r ?BigCf.BCA.big1_seq ?addr0;
  1, 2: by smt(coeff_polyXn mem_filter mem_range mul0r range_uniq rem_filter).
by smt(mulrC mulr0 subrr gedeg_coeff).
qed.

lemma ltn_rmodpN0 p q : q <> poly0 => deg (rmodp p q) < deg q
  by smt(ltn_rmodp).

lemma rmodp1 p : rmodp p poly1 = poly0
  by smt(deg1 deg_eq0 ge0_deg ltn_rmodp oner_neq0).

lemma rmodp_small p q : deg p < deg q => rmodp p q = p.
proof.
rewrite /rmodp /redivp /redivp_rec /=; case: (q = poly0) => //= q_neq0.
by move => degP; rewrite iter_id //= /redivp_rec_it /= degP.
qed.

lemma leq_rmodp m d : deg (rmodp m d) <= deg m
  by smt(ltn_rmodpN0 rmodp0 rmodp_small).

lemma rmodpC p c : c <> zeror => rmodp p (polyC c) = poly0
  by smt(degC deg_gt0 ge0_deg ltn_rmodpN0).

lemma rdvdp0 d : rdvdp d poly0 by smt(rmod0p).

lemma rdvd0p n : rdvdp poly0 n = (n = poly0) by smt(rmodp0).

(* skip? *)
lemma rdvd0pP n : (n = poly0) = rdvdp poly0 n by smt(rdvd0p).

lemma rdvdpN0 p q : rdvdp p q => q <> poly0 => p <> poly0 by smt(rdvd0p).

lemma rdvdp1 d : rdvdp d poly1 = (deg d = 1).
proof.
rewrite /rdvdp; case: (d = poly0); 1: by smt(deg0 onep_neq0 rmodp0).
case: (1 < deg d); 1: by smt(deg0 deg1 rmodp_small).
by smt(deg_eq1 deg_gt0 rmodpC).
qed.

lemma rdvd1p m : rdvdp poly1 m by smt(rmodp1).

lemma Nrdvdp_small n d :
  n <> poly0 => deg n < deg d => rdvdp d n = false by smt(rmodp_small).

lemma rmodp_eq0P p q : (rmodp p q = poly0) = (rdvdp q p) by smt().

lemma rmodp_eq0 p q : rdvdp q p => rmodp p q = poly0 by smt().

lemma rdvdp_leq p q : rdvdp p q => q <> poly0 => deg p <= deg q
  by smt(rmodp_small).

(* It will go through useless loops once "rmodd pp qq = poly0"
   since iter is needed as recursive calls are currently not allowed. *)
op rgcdp_it (i : poly * poly) =
  let (pp, qq) = i in
  if qq = poly0 then i else
  let rr = rmodp pp qq in
  (qq, rr).

op rgcdp (p q : poly) =
  let (p1, q1) = if deg p < deg q then (q, p) else (p, q) in
  if p1 = poly0 then q1 else
  let (p2, q2) = iter (deg p1) rgcdp_it (p1, q1) in
  if q2 = poly0 then p2 else q2.

lemma rgcd0p : left_id poly0 rgcdp.
proof.
move => p; rewrite /rgcdp deg0 deg_gt0; case: (p = poly0) => [/#|p_neq0].
by rewrite /= p_neq0 /= /rgcdp_it iter_id.
qed.

lemma rgcdp0 : right_id poly0 rgcdp
  by move => p; move: (rgcd0p p); smt(deg0 deg_gt0).

lemma rgcdpE p q :
  rgcdp p q = if deg p < deg q
    then rgcdp (rmodp q p) p else rgcdp (rmodp p q) q.
proof.
have rgcdp_itP : forall m n i, deg (snd i) <= m => deg (snd i) <= n =>
                               deg (snd i) < deg (fst i) =>
                               iter m rgcdp_it i = iter n rgcdp_it i.
- suff /# : forall m n i, deg (snd i) <= m => deg (snd i) <= n =>
                          deg (snd i) < deg (fst i) => m < n =>
                          iter m rgcdp_it i = iter n rgcdp_it i.
  move => m n {p q} i; have [p q pqP] : exists p q, i = (p, q) by smt().
  rewrite pqP /= => {pqP i} mP; move: n p; have m_ge0 : 0 <= m by smt(ge0_deg).
  move: m m_ge0 q mP; apply: intind; 1: by smt(deg_gt0 iter0 iter_id).
  move => /= m m_ge0 mh q mqP n p nqP pqP mnP.
  have: exists n', n' + 1 = n /\ deg q <= n' + 1 /\ m < n' by smt().
  move => [n' [nn'P [n'qP mn'P]]]; rewrite -nn'P; move => {n nqP mnP nn'P}.
  rewrite !iterSr //; 1: by smt(ge0_deg).
  move: n' n'qP mn'P => n nqP mnP; pose i := rgcdp_it (p, q).
  have -> : i = (fst i, snd i) by smt().
  by apply: mh; smt(deg0 ltn_rmodpN0).
case: (p = poly0) => p_neq0; 1: by smt(rgcd0p rmod0p).
case: (q = poly0) => q_neq0; 1: by smt(rgcd0p rmod0p).
case: (deg p = deg q) => degpqP.
- rewrite {1}/rgcdp degpqP /= p_neq0 /=.
  have [d dP] : exists d, d + 1 = deg p by smt().
  by smt(deg_gt0 iterSr ltn_rmodpN0).
suff /# : forall p q, q <> poly0 => deg q < deg p =>
                      rgcdp p q = rgcdp (rmodp p q) q.
move => {p q p_neq0 q_neq0 degpqP} p q p_neq0 degpqP.
rewrite {1}/rgcdp; have -> /= : ! deg p < deg q by smt().
have -> /= : p <> poly0 by smt(deg_gt0).
have [d dP] : exists d, d + 1 = deg p by smt().
by smt(deg_gt0 iterSr ltn_rmodpN0).
qed.

op redivp_spec (m d : poly) (i : int * poly * poly) =
  let (k, q, r) = i in
  (d <> poly0 => deg r < deg d) /\
  (d * polyC (lc d) = polyC (lc d) * d =>
   m * polyC (exp (lc d) k) = q * d + r).

(* PolyComRing.mulrC used! *)
lemma redivpP m d : redivp_spec m d (redivp m d).
proof.
rewrite /redivp_spec; case: (d = poly0) => [|d_neq0 /=];
  1: by move => -> /= _; rewrite PS.mulr0 PS.add0r expr0 PS.mulr1.
case: (d * polyC (lc d) = polyC (lc d) * d) =>[dP /=|]; 2: by smt(ltn_rmodpN0).
suff: let (k, q, r) = redivp m d in
      m * polyC (exp (lc d) k) = q * d + r by smt(ltn_rmodpN0).
suff: forall n i i' k qq r,
        i = (k, qq, r, d, deg d, lc d) => deg r <= n =>
        0 <= k => m * polyC (exp (lc d) k) = qq * d + r =>
        i' = iter n redivp_rec_it (k, qq, r, d, deg d, lc d) =>
        forall k' qq' r' d' sq' cq', i' = (k', qq', r', d', sq', cq') =>
          m * polyC (exp (lc d) k') = qq' * d + r'.
- move => nP; pose i := (0, poly0, m, d, deg d, lc d).
  pose i' := iter (deg m) redivp_rec_it i; move: (nP (deg m) i i').
  have -> : redivp m d = let (k, qq, r, q, sq, cq) = i' in (k, qq, r) by smt().
  suff /# : m * polyC (exp (lc d) 0) = poly0 * d + m.
  by smt(expr0 PS.mulr1 PS.mul0r PS.add0r).
apply: natind => [|n n_ge0 /= nh i i'' k qq r iP nP k_ge0 mP]; 1: by smt(iter0).
rewrite iterSr // => i''P; pose i' := redivp_rec_it i.
case: (deg r < deg d) => degdrP; 1: by by smt(iter_id).
suff /# : let (k', qq', r', q', sq', cq') = i' in
          deg r' <= n /\ m * polyC (exp (lc d) k') = qq' * d + r'.
pose k'  := let (k, qq, r, q, sq, cq) = i' in k.
pose qq' := let (k, qq, r, q, sq, cq) = i' in qq.
pose r'  := let (k, qq, r, q, sq, cq) = i' in r.
pose p := (lc r) ** polyXn (deg r - deg d).
have rP : r' = r  * polyC (lc d) - p * d by smt().
suff: deg r' <= n; 1: suff /# : m * polyC (exp (lc d) k') = qq' * d + r'.
- case: (deg r < deg d) => [/#|degP].
  have [-> ->] : k'  = k + 1 /\ qq' = qq * polyC (lc d) + p by smt().
  rewrite rP exprSr // polyCM PS.mulrA mP !PS.mulrDl -PS.mulrA dP.
  by smt(PS.addrCA PS.addr0 PS.mulrA PS.subrr).
rewrite rP deg_leP // => j jP; rewrite polyDE polyNE.
rewrite PS.mulrC /p scalepE -PS.mulrA -!scalepE !polyZE.
rewrite polyME (BigCf.BCA.big_rem _ _ _ (deg r - deg d)) /predT /=;
  1: by smt(deg_gt0 mem_range).
rewrite coeff_polyXn /= ?mul1r ?BigCf.BCA.big1_seq ?addr0;
  1, 2: by smt(coeff_polyXn mem_filter mem_range mul0r range_uniq rem_filter).
have {nP} : deg r <= n \/ deg r = n + 1 by smt().
move =>[|nP]; 1: by smt(add0r mulr0 oppr0 gedeg_coeff).
by smt(add0r mulrC mulr0 oppr0 subrr gedeg_coeff).
qed.

lemma rmodpp p :
  p * (polyC (lc p)) = (polyC (lc p)) * p => rmodp p p = poly0.
proof.
case: (p = poly0) => p_neq0; 1: by smt(rmodp0).
rewrite /rmodp /redivp p_neq0 /= /redivp_rec /redivp_rec_it.
have [d [dP d_ge0]] : exists d, deg p = d + 1 /\ 0 <= d by smt(deg_gt0).
rewrite dP /= iterSr //= dP subrr -addrA subrr addr0 !scalepE polyXn0.
rewrite PS.mul0r PS.mulr1 PS.add0r => ->.
by rewrite PS.subrr /= iter_id; smt(deg0).
qed.

op rcoprimep p q = deg (rgcdp p q) = 1.

op eqpoly0p p = if p = poly0 then poly1 else poly0.

(* It will go through useless loops once "rcoprimep p q"
   since iter is needed as recursive calls are currently not allowed. *)
op rgdcop_rec_it (i : poly * poly) =
  let (q, p) = i in
  if  rcoprimep p q then i else
  (q, (rdivp p (rgcdp p q))).

op rgdcop (q p : poly) =
  let (qq, pp) = iter (deg p) rgdcop_rec_it (q, p) in
  if rcoprimep pp qq then pp else eqpoly0p qq.

lemma rgdcop0 q : rgdcop q poly0 = eqpoly0p q by smt(deg0 deg_gt0 iter0).

end RingPseudoDivision.

abstract theory ComRegDivisor.

type coeff, poly.

clone ComRing as CR with type t <= coeff.

clone PolyComRing as PCR with
  type   coeff <= coeff,
  type   poly  <= poly,
  theory Coeff <- ComRegDivisor.CR.

clone ComRegDivisor.PCR.PolyComRing as PS.

clone RingPseudoDivision as RPD with
  type   coeff <= coeff,
  type   poly  <= poly,
  theory CR    <- ComRegDivisor.CR,
  theory PCR   <- ComRegDivisor.PCR,
  theory PS    <- ComRegDivisor.PS.

import ComRegDivisor.CR.
import ComRegDivisor.PCR.
import ComRegDivisor.RPD.

(* To backport *)
lemma commrX (p q : poly) (n : int) :
  0 <= n => p * q = q * p => p * PS.exp q n = PS.exp q n * p.
proof.
move: n; apply: intind; 2: by smt(PS.exprS PS.mulrA).
by rewrite /= PS.expr0 PS.mulr1 PS.mul1r.
qed.

lemma rreg_div0 q r d :
  injective (transpose CR.( * ) (lc d)) => deg r < deg d =>
  (q * d + r = poly0) = (q = poly0 && r = poly0).
proof.
move => rreg_d lt_r_d; rewrite PS.addrC PS.addr_eq0.
case: (q = poly0) => [|q_neq0]; 1: by smt(PS.mul0r PS.oppr0).
suff: deg d <= deg (q * d) by smt(degN).
by rewrite degM_proper; smt(deg_ge1 lc_eq0 mul0r).
qed.

(* Fix so that one can use polyCX from Poly.ec *)
lemma polyCX c i : 0 <= i => PS.exp (polyC c) i = polyC (exp c i).
proof.
elim: i => [|i ge0_i ih]; first by rewrite expr0 PS.expr0.
by rewrite exprS ?PS.exprS // ih polyCM.
qed.

lemma redivp_eq d q r :
  d * polyC (lc d) = polyC (lc d) * d =>
  injective (transpose CR.( * ) (lc d)) =>
  deg r < deg d =>
  let k = rscalp (q * d + r) d in
  let c = polyC (CR.exp (lc d) k) in
  redivp (q * d + r) d = (k, q * c, r * c).
proof.
move => Cdl Rreg degrdP; have d_neq0 : d <> poly0 by smt(deg_gt0).
pose k := rscalp (q * d + r) d; pose c := polyC (CR.exp (lc d) k).
pose qq := rdivp (q * d + r) d; pose rr := rmodp (q * d + r) d.
suff /# : qq = q * c /\ rr = r * c.
have e : (q * d + r) * c = qq * d + rr by smt(redivpP ltn_rmodpN0).
have e' : q * d * c = q * c * d
  by smt(commrX PS.mulrA polyCX rscalp_ge0).
suff: qq = q * c by smt(PS.addrI PS.mulrDl).
have {e'} : (qq - q * c) * d = r * c - rr.
- rewrite PS.mulrBl PS.subr_eq -e' PS.addrAC.
  by smt(PS.addrC PS.mulrDl PS.subr_eq).
rewrite -PS.subr_eq0 PS.opprB.
suff: deg (rr - r * c) < deg d by smt(rreg_div0 PS.subr_eq0).
suff: deg (r * c) < deg d by smt(redivpP degB).
by smt(degC degM_le deg0 deg_gt0 PS.mulr0 PS.mul0r).
qed.

lemma rdivp_eq d p :
  d * polyC (lc d) = polyC (lc d) * d =>
  p * polyC (exp (lc d) (rscalp p d)) = (rdivp p d) * d + (rmodp p d)
  by smt(redivpP).

lemma rreg_lead0 p : injective (transpose CR.( * ) (lc p)) => p <> poly0
  by smt(lc_eq0 mulr0 oner_neq0).

lemma rreg_deg c p :
  injective (transpose CR.( * ) c) => deg (p * polyC c) = deg p
  by smt(mulr0 oner_neq0 degC degM_proper lcC lc_eq0 mul0r PS.mul0r).

lemma rreg_polyMC_eq0 c p :
  injective (transpose CR.( * ) c) => (p * polyC c = poly0) = (p = poly0)
  by smt(deg_eq0 rreg_deg).

(* TODO: Prove other rreg lemmas using lemmas about lreg *)
lemma rregX c n :
  0 <= n => injective (transpose CR.( * ) c) =>
  injective (transpose CR.( * ) (exp c n)) by smt(lregXn mulrC).

lemma eq_rdvdp d k q1 p :
  d * polyC (lc d) = polyC (lc d) * d =>
  injective (transpose CR.( * ) (lc d)) =>
  0 <= k => p * polyC (CR.exp (lc d) k) = q1 * d => rdvdp d p.
proof.
move => Cdl; pose ld := lc d; pose v := rscalp p d; pose m := max v k.
pose ld_mMv := polyC (exp ld (m - v)); move => Rreg k_ge0 he.
pose ld_mMk := polyC (exp ld (m - k)).
rewrite /rdvdp -(rreg_polyMC_eq0 _ _ (rregX _ (m - v) _ Rreg)) => [/#|].
suff: ((rdivp p d) * ld_mMv - q1 * ld_mMk) * d + (rmodp p d) * ld_mMv = poly0
  by rewrite rreg_div0 // rreg_deg ?ltn_rmodp ?rreg_lead0 //; smt(rregX).
suff: rdivp p d * ld_mMv * d + rmodp p d * ld_mMv = q1 * ld_mMk * d
  by smt(PS.addrA PS.addrC PS.mulrBl PS.subr_eq0).
have -> : q1 * ld_mMk * d = q1 * d * ld_mMk
  by smt(commrX PS.mulrA polyCX).
have -> : rdivp p d * ld_mMv * d = rdivp p d * d * ld_mMv
  by smt(commrX PS.mulrA polyCX).
rewrite -he -PS.mulrDl -rdivp_eq ?Cdl //.
by rewrite -!PS.mulrA -!polyCM -!exprD_nneg; smt(rscalp_ge0).
qed.

op rdvdp_spec (p q r : poly) (b : bool) : bool =
  (exists k q1, p * polyC (exp (lc q) k) = q1 * q) && r = poly0 && b ||
  r = rmodp p q && r <> poly0 && ! b.

lemma rdvdp_eqP d p :
  d * polyC (lc d) = polyC (lc d) * d =>
  injective (transpose CR.( * ) (lc d)) =>
  rdvdp_spec p d (rmodp p d) (rdvdp d p).
proof.
case: (rdvdp d p) => [hdvd Cdl|]; 2: by smt(rreg_lead0).
suff /# : p * polyC (exp (lc d) (rscalp p d)) = rdivp p d * d.
by rewrite rdivp_eq; smt(PS.addr0 rmodp_eq0P).
qed.

lemma rdvdp_mulr d p :
  d * polyC (lc d) = polyC (lc d) * d =>
  injective (transpose CR.( * ) (lc d)) =>
  rdvdp d (p * d)
  by move => 2?; rewrite (eq_rdvdp d 0 p) ?expr0 ?PS.mulr1 /#.

lemma rmodp_mulr d p :
  d * polyC (lc d) = polyC (lc d) * d =>
  injective (transpose CR.( * ) (lc d)) =>
  rmodp (p * d) d = poly0 by smt(rdvdp_mulr).

lemma rmodpp d :
  d * polyC (lc d) = polyC (lc d) * d =>
  injective (transpose CR.( * ) (lc d)) =>
  rmodp d d = poly0 by smt(PS.mul1r rmodp_mulr).

lemma mulrI0_rreg (p : poly) :
  (forall q, q * p = poly0 => q = poly0) =>
  injective (transpose PS.( * ) p).
proof.
move=> reg_p q r qrP; rewrite -PS.subr_eq0 &(reg_p).
by rewrite PS.mulrBl; smt(PS.subrr).
qed.

lemma rreg_lead p :
  injective (transpose CR.( * ) (lc p)) =>
  injective (transpose PS.( * )     p)
  by smt(lcM_proper lc_eq0 mulrI0_rreg mul0r).

lemma rdivpp d :
  d * polyC (lc d) = polyC (lc d) * d =>
  injective (transpose CR.( * ) (lc d)) =>
  rdivp d d = polyC (exp (lc d) (rscalp d d)).
proof.
move => Cdl Rreg; move: (rdivp_eq d d Cdl); rewrite rmodpp ?Cdl //.
by rewrite PS.addr0 -polyCX ?commrX ?polyCX; smt(rscalp_ge0 rreg_lead).
qed.

lemma rdvdpp d :
  d * polyC (lc d) = polyC (lc d) * d =>
  injective (transpose CR.( * ) (lc d)) =>
  rdvdp d d by smt(rmodpp).

lemma rdivpK d p :
  d * polyC (lc d) = polyC (lc d) * d =>
  injective (transpose CR.( * ) (lc d)) =>
  rdvdp d p =>
  rdivp p d * d = p * polyC (CR.exp (lc d) (rscalp p d))
  by smt(PS.addr0 rdivp_eq).

end ComRegDivisor.

abstract theory RingMonic.

type coeff, poly.

clone ComRing as CR with type t <= coeff.

clone PolyComRing as PCR with
  type   coeff <= coeff,
  type   poly  <= poly,
  theory Coeff <- RingMonic.CR.

clone RingMonic.PCR.PolyComRing as PS.

clone RingPseudoDivision as RPD with
  type   coeff <= coeff,
  type   poly  <= poly,
  theory CR    <- RingMonic.CR,
  theory PCR   <- RingMonic.PCR,
  theory PS    <- RingMonic.PS.

clone ComRegDivisor as CRD with
  type   coeff <= coeff,
  type   poly  <= poly,
  theory CR    <- RingMonic.CR,
  theory PCR   <- RingMonic.PCR,
  theory PS    <- RingMonic.PS,
  theory RPD   <- RingMonic.RPD.

import RingMonic.CR.
import RingMonic.PCR.
import RingMonic.RPD.
import RingMonic.CRD.

lemma monic_comreg p :
  lc p = oner =>
  p * polyC (lc p) = polyC (lc p) * p /\
  injective (transpose CR.( * ) (lc p))
  by smt(mulr1 PS.mulr1 PS.mul1r).

lemma redivp_eq d q r :
  lc d = oner =>
  deg r < deg d =>
  let k = rscalp (q * d + r) d in
  redivp (q * d + r) d = (k, q, r)
  by smt(expr1z monic_comreg PS.mulr1 redivp_eq).

lemma rdivp_eq d p : lc d = oner => p = rdivp p d * d + rmodp p d
  by smt(expr1z monic_comreg PS.mulr1 rdivp_eq).

lemma rdivpp d : lc d = oner => rdivp d d = poly1
  by smt(expr1z monic_comreg rdivpp).

lemma rdivp_addl_mul_small d q r :
  lc d = oner => deg r < deg d => rdivp (q * d + r) d = q
  by smt(monic_comreg redivp_eq).

lemma rdivp_addl_mul d q r :
  lc d = oner => rdivp (q * d + r) d = q + rdivp r d.
proof.
move => mond; move: (monic_comreg d mond) => [Cdl Rreg].
rewrite {1}(rdivp_eq d r) // PS.addrA -PS.mulrDl.
by rewrite rdivp_addl_mul_small; smt(ltn_rmodp rreg_lead0).
qed.

lemma rdivpDl d q r :
  lc d = oner => rdvdp d q => rdivp (q + r) d = rdivp q d + rdivp r d.
proof.
move => mond; move: (monic_comreg d mond) => [Cdl Rreg].
rewrite {1}(rdivp_eq d r) // PS.addrA {2}(rdivp_eq d q) // -rmodp_eq0P.
move => ->; rewrite PS.addr0 -PS.mulrDl.
by rewrite rdivp_addl_mul_small // ltn_rmodp rreg_lead0 // Rreg.
qed.

lemma rdivpDr d q r :
  lc d = oner => rdvdp d r => rdivp (q + r) d = rdivp q d + rdivp r d
  by smt(PS.addrC rdivpDl).

lemma rdivp_mull d p : lc d = oner => rdivp (p * d) d = p
  by smt(PS.addr0 rdiv0p rdivp_addl_mul).

lemma rmodp_mull d p : lc d = oner => rmodp (p * d) d = poly0
  by smt(monic_comreg rmodp_mulr).

lemma rmodpp d : lc d = oner => rmodp d d = poly0
  by smt(monic_comreg rmodpp).

lemma rmodp_addl_mul_small d q r :
  lc d = oner => deg r < deg d => rmodp (q * d + r) d = r
  by smt(monic_comreg redivp_eq).

lemma rmodpD (d p q : poly) :
  lc d = oner => rmodp (p + q) d = rmodp p d + rmodp q d.
proof.
move => mond; move: (monic_comreg d mond) => [Cdl Rreg].
rewrite {1}(rdivp_eq d p) // {1}(rdivp_eq d q) // PS.addrACA.
by rewrite  -PS.mulrDl rmodp_addl_mul_small; smt(degD ltn_rmodpN0 rreg_lead0).
qed.

lemma rmodp_mulmr d p q :
  lc d = oner => rmodp (p * rmodp q d) d = rmodp (p * q) d.
proof.
move => mond; move: (monic_comreg d mond) => [Cdl Rreg].
rewrite {2}(rdivp_eq d q) // PS.mulrDr rmodpD //.
by rewrite PS.mulrA rmodp_mull // PS.add0r.
qed.

lemma rdvdpp d : lc d = oner => rdvdp d d by smt(monic_comreg rdvdpp).

lemma eq_rdvdp d q1 p : lc d = oner => p = q1 * d => rdvdp d p
  by smt(eq_rdvdp expr1z monic_comreg PS.mulr1).

lemma rdvdp_mulr d p : lc d = oner => rdvdp d (p * d)
  by smt(monic_comreg rdvdp_mulr).

lemma rdivpK d p : lc d = oner => rdvdp d p => (rdivp p d) * d = p
  by smt(PS.addr0 rdivp_eq rmodp_eq0).

lemma rdivp1 p : rdivp p poly1 = p by smt(lc1 PS.mulr1 rdivp_mull).

op prepolyDrop (k : int) (p : poly) =
  fun i => if 0 <= i < deg p - k /\ 0 <= k then p.[i + k] else zeror.

lemma ispolyDrop (k : int) (p : poly) : ispoly (prepolyDrop k p)
  by split => @/prepolyDrop; smt(gedeg_coeff).

op drop_poly k p = to_polyd (prepolyDrop k p).

lemma drop_poly_lt0 n p : n < 0 => drop_poly n p = poly0
  by rewrite poly_eqP => n_lt0 i iP; rewrite coeffE ?ispolyDrop poly0E /#.

op prepolyTake (k : int) (p : poly) =
  fun i => if 0 <= i < k then p.[i] else zeror.

lemma ispolyTake (k : int) (p : poly) : ispoly (prepolyTake k p)
  by split => @/prepolyTake; smt(gedeg_coeff).

op take_poly k p = to_polyd (prepolyTake k p).

lemma take_poly_lt0 n p : n < 0 => take_poly n p = poly0
  by rewrite poly_eqP => n_lt0 i iP; rewrite coeffE ?ispolyTake poly0E /#.

lemma size_take_poly n p : 0 <= n => deg (take_poly n p) <= n
  by smt(coeffE deg_leP ispolyTake).

lemma poly_take_drop n p :
  0 <= n => take_poly n p + drop_poly n p * (polyXn n) = p.
proof.
rewrite poly_eqP => n_ge0 i i_ge0; rewrite polyDE polyME; case: (i < n) => inP.
- rewrite BigCf.BCA.big1_seq; 2: by smt(addr0 coeffE ispolyTake).
  rewrite /predT /= => j; rewrite !coeffE; 1, 2: by smt(ispolyDrop ispolyXn).
  by smt(mulr0 mem_range).
- have -> : (take_poly n p).[i] = zeror by smt(coeffE ispolyTake).
  rewrite add0r (BigCf.BCA.big_rem _ _ _ (i - n)); 1: smt(mem_range).
  rewrite /predT /= coeff_polyXn //=; have {3}-> /= : n = i - (i - n) by smt().
  rewrite BigCf.BCA.big1_seq ?addr0 ?mulr1;
    1: by smt(coeff_polyXn mem_filter mem_range mulr0 range_uniq rem_filter).
  by rewrite coeffE ?ispolyDrop /prepolyDrop; smt(gedeg_coeff).
qed.

lemma drop_poly_rdivp n p : drop_poly n p = rdivp p (polyXn n).
proof.
case: (0 <= n) => [n_ge0|]; last first.
- suff: n < 0 => polyXn n = poly0 by smt(drop_poly_lt0 rdivp0).
  by smt(coeffE ispolyXn poly0E poly_eqP).
- have mond: lc (polyXn n) = oner by apply (lcXn _ n_ge0).
  rewrite -{2}(poly_take_drop n p n_ge0) PS.addrC rdivp_addl_mul //.
  by rewrite rdivp_small ?PS.addr0 // degXn; smt(size_take_poly).
qed.

lemma take_poly_rmodp n p : 0 <= n => take_poly n p = rmodp p (polyXn n).
proof.
move => n_ge0; have mond: lc (polyXn n) = oner by apply (lcXn _ n_ge0).
rewrite -{2}(poly_take_drop n p n_ge0) rmodpD // rmodp_small ?rmodp_mull;
by smt(degXn size_take_poly PS.addr0).
qed.

lemma peval0 x : peval poly0 x = zeror
  by rewrite /peval deg0 range_geq.

lemma pevalC c x : peval (polyC c) x = c
  by rewrite /peval degC; smt(BigCf.BCA.big_int1 expr0 mulr1 polyCE range_geq).

lemma pevalX x : peval X x = x.
proof.
rewrite /peval degX; have -> : range 0 2 = [0; 1] by smt(rangeS rangeSr).
rewrite !BigCf.BCA.big_cons BigCf.BCA.big_nil /predT /= addr0 !polyXE.
by rewrite expr0 expr1 /= mul0r mul1r add0r.
qed.

lemma pevalD (p q : poly) x :
  peval (p + q) x = peval p x + peval q x.
proof.
pose pf := fun (i : int) => p.[i] * (exp x i).
have -> : peval p x = BigCf.BCA.bigi predT pf 0 (max (deg p) (deg q)).
- rewrite /peval eq_sym (BigCf.BCA.big_cat_int (deg p));
  smt(addr0 BigCf.BCA.big1_seq gedeg_coeff ge0_deg mem_range mul0r).
pose qf := fun (i : int) => q.[i] * (exp x i).
have -> : peval q x = BigCf.BCA.bigi predT qf 0 (max (deg p) (deg q)).
- rewrite /peval eq_sym (BigCf.BCA.big_cat_int (deg q));
  smt(addr0 BigCf.BCA.big1_seq gedeg_coeff ge0_deg mem_range mul0r).
rewrite -BigCf.BCA.big_split /peval eq_sym.
case: (deg (p + q) < max (deg p) (deg q)); 2: by smt(degD mulrDl polyDE).
move => ?; rewrite (BigCf.BCA.big_cat_int (deg (p + q))); 1, 2: by smt(ge0_deg).
have -> : (fun i => (p + q).[i] * (exp x i)) =
          (fun i => (pf i) + (qf i)) by smt(mulrDl polyDE).
rewrite -subr_eq0 addrAC subrr add0r.
rewrite BigCf.BCA.big1_seq //= => i [_ ]; rewrite mem_range /pf /qf.
by rewrite -mulrDl -polyDE; smt(gedeg_coeff mul0r).
qed.

lemma drop_polyn0 n : 0 <= n => drop_poly n poly0 = poly0
  by rewrite poly_eqP; smt(coeffE deg0 ispolyDrop poly0E).

lemma drop_poly0p p : drop_poly 0 p = p
  by smt(coeffE gedeg_coeff ispolyDrop poly_eqP).

lemma drop_poly_eq0 n p : deg p <= n => drop_poly n p = poly0
  by smt(coeffE ispolyDrop poly0E poly_eqP).

lemma coef_drop_poly n p i :
  0 <= n => 0 <= i => (drop_poly n p).[i] = p.[i + n]
  by rewrite coeffE ?ispolyDrop /prepolyDrop; smt(gedeg_coeff).

lemma drop_polyD m n p :
  0 <= m => 0 <= n => drop_poly m (drop_poly n p) = drop_poly (m + n) p
  by smt(coef_drop_poly poly_eqP).

lemma deg_drop_poly p n : 0 <= n => deg (drop_poly n p) = max 0 (deg p - n).
proof.
suff /# : forall m n p, 0 <= n => deg p <= m =>
                        deg (drop_poly n p) = max 0 (deg p - n).
apply: natind; 1: by smt(deg0 deg_eq0 ge0_deg drop_polyn0).
move => /= {n p} m m_ge0 mh n p n_ge0 degmpP.
case: (deg p <= n); 1: by smt(deg0 drop_poly_eq0).
move => degnpP; have {degnpP} degnpP : n < deg p by smt().
case: (0 = n) => [|n_neq0]; 1: by smt(drop_poly0p ge0_deg).
have {n_neq0 n_ge0} n_gt0 : 0 < n by smt().
have -> : drop_poly n p = drop_poly (n - 1) (drop_poly 1 p) by smt(drop_polyD).
suff /# : deg (drop_poly 1 p) = deg p - 1.
rewrite (degP (drop_poly 1 p) (deg p - 1));
by smt(coef_drop_poly deg_eq0 gedeg_coeff lc_eq0).
qed.

lemma pevalMX (p : poly) x :
  peval (p * X) x = (peval p x) * x.
proof.
rewrite /peval BigCf.BCA.big_distrl ?mul0r ?mulrDl.
case: (p = poly0) => [->|p_neq0]; 1: by smt(deg0 PS.mul0r range_geq).
rewrite range_ltn; 1: by smt(degM_proper degX ge0_deg lcX lc_eq0 mulr1).
have -> : deg (p * X) = deg p + 1
  by rewrite degM_proper ?lcX ?degX // mulr1 lc_eq0.
rewrite BigCf.BCA.big_cons /predT /= polyMXE lt0_coeff // mul0r.
rewrite add0r -/predT (range_add 0 (deg p) 1) BigCf.BCA.big_map.
apply BigCf.BCA.eq_big_seq => i iP /=; rewrite /(\o) -mulrA.
by rewrite -exprSr ?polyMXE; smt(mem_range).
qed.

lemma pevalZ (c : coeff) (p : poly) x :
  peval (c ** p) x = c * (peval p x).
proof.
suff: forall n c p x, deg p <= n =>
        peval (c ** p) x = c * (peval p x) by smt(ge0_deg).
apply: natind; 1: by smt(deg_eq0 ge0_deg mulr0 scalep0 peval0).
move => /= n n_ge0 nh {c p x} c p x degnpP.
rewrite -{1}(poly_take_drop 1 p) //.
rewrite scalepDr pevalD (scalepE _ (_ * X)) PS.mulrA -scalepE pevalMX.
have -> : peval (c ** take_poly 1 p) x = c * p.[0].
- have -> : take_poly 1 p = polyC p.[0]
    by rewrite poly_eqP => i i_ge0; rewrite !coeffE ?ispolyTake ?ispolyC /#.
  rewrite scalepE -polyCM /peval degC.
  case: (c * p.[0] = zeror); 1: by smt(BigCf.BCA.big_geq).
  by rewrite rangeS BigCf.BCA.big_seq1 /= expr0 mulr1 polyCE.
case: (p = poly0) => [->|p_neq0].
- by rewrite poly0E drop_polyn0 // scalep0 !peval0 mul0r addr0.
- rewrite nh ?deg_drop_poly -?mulrA -?mulrDr //; 1: by smt().
  rewrite -subr_eq0 -mulrBr -pevalMX.
  suff -> : p.[0] = peval (take_poly 1 p) x
    by rewrite -pevalD poly_take_drop // subrr mulr0.
  case: (p.[0] = zeror) => [?|p0_neq0]; rewrite /peval.
  + suff -> : deg (take_poly 1 p) = 0 by rewrite range_geq.
    by rewrite deg_eq0 poly_eqP => i iP; rewrite poly0E coeffE; smt(ispolyTake).
  + have -> : deg (take_poly 1 p) = 1 by apply degP; smt(coeffE ispolyTake).
    by smt(BigCf.BCA.big_seq1 coeffE expr0 ispolyTake mulr1 rangeS).
qed.

lemma pevalN (p : poly) x : peval (-p) x = - peval p x.
proof.
suff -> : -p = (- oner) ** p by rewrite pevalZ mulN1r.
by rewrite scaleNp scalepE PS.mul1r.
qed.

lemma pevalB (p q : poly) x :
  peval (p - q) x = peval p x - peval q x by smt(pevalD pevalN).

lemma pevalM (p q : poly) x :
  peval (p * q) x = peval p x * peval q x.
proof.
suff: forall n p q x, deg p <= n =>
        peval (p * q) x = peval p x * peval q x by smt(ge0_deg).
apply: natind; 1: by smt(deg_eq0 ge0_deg mul0r PS.mul0r peval0).
move => /= n n_ge0 nh {p q x} p q x pP; rewrite -{1}(poly_take_drop 1 p) //.
have cP : take_poly 1 p = polyC p.[0]
  by rewrite poly_eqP => i i_ge0; rewrite !coeffE ?ispolyTake ?ispolyC /#.
rewrite cP PS.mulrDl pevalD -scalepE pevalZ -PS.mulrA.
rewrite (PS.mulrC X) nh ?pevalMX; 1: by smt(deg_drop_poly).
rewrite mulrCA (mulrC (peval q x)) -mulrDl -pevalMX.
suff /# : p.[0] + peval (drop_poly 1 p * X) x = peval p x.
suff -> : p.[0] = peval (take_poly 1 p) x by rewrite -pevalD poly_take_drop.
case: (p.[0] = zeror) => p0P; rewrite /peval.
- suff -> : deg (take_poly 1 p) = 0 by rewrite range_geq.
  by rewrite deg_eq0 poly_eqP => i iP; rewrite poly0E coeffE; smt(ispolyTake).
- have -> : deg (take_poly 1 p) = 1 by apply degP; smt(coeffE ispolyTake).
  by smt(BigCf.BCA.big_seq1 coeffE expr0 ispolyTake mulr1 rangeS).
qed.

lemma root_XsubC a x : root (X - polyC a) x = (x = a).
proof.
rewrite /peval; have -> : deg (X - polyC a) = 0 + 1 + 1.
- apply degP; 1, 3: by smt(degB degX degC_le gedeg_coeff).
  by rewrite polyDE polyXE polyNE polyCE /= subr0 oner_neq0.
rewrite !BigCf.BCA.big_int_recr ?range_geq ?BigCf.BCA.big_nil //=.
rewrite !polyDE !polyXE !polyNE !polyCE /= !add0r subr0.
rewrite expr0 expr1 mulr1 mul1r.
by rewrite addrC subr_eq0.
qed.

lemma rootMl (p q : poly) r : root p r => root (p * q) r
  by smt(mul0r pevalM).

lemma rootMr (p q : poly) r : root q r => root (p * q) r
  by smt(mulr0 pevalM).

lemma factor_theorem p r : root p r = exists q, p = q * (polyX - polyC r).
proof.
rewrite eqboolP; split => [prP|]; 2: by smt(rootMr root_XsubC).
pose preQ := fun i => if 0 <= i < deg p then peval (drop_poly (i + 1) p) r
                                        else zeror.
have isprepolyQ : ispoly preQ by split => @/prepolyTake; smt(gedeg_coeff).
exists (to_polyd preQ); rewrite PS.mulrBr poly_eqP => i iP.
rewrite polyDE polyNE polyMXE PS.mulrC -scalepE polyZE !coeffE //.
rewrite /preQ; case: (i < deg p); last first.
- by smt(drop_poly_eq0 gedeg_coeff mulr0 peval0 subr0).
- move => degipP; have -> /= : i - 1 < deg p by smt().
  case: (i = 0) => [i_eq0|i_neq0]; rewrite ?i_eq0 /=.
  + rewrite add0r mulrC -pevalMX -subr_eq0 opprK.
    suff -> : p.[0] = peval (take_poly 1 p) r by smt(pevalD poly_take_drop).
    rewrite /peval; case: (p.[0] = zeror) => p0P.
    * suff -> : deg (take_poly 1 p) = 0 by rewrite range_geq.
      by rewrite deg_eq0 poly_eqP; smt(coeffE ispolyTake poly0E).
    * have -> : deg (take_poly 1 p) = 1 by apply degP; smt(coeffE ispolyTake).
      by smt(BigCf.BCA.big_seq1 coeffE expr0 ispolyTake mulr1 rangeS).
  + rewrite iP; have -> /= : 0 <= i - 1 by smt().
    rewrite mulrC -pevalMX -pevalB addrC -drop_polyD //.
    rewrite -{1}(poly_take_drop 1 (drop_poly i p)) // -PS.addrA.
    rewrite PS.subrr PS.addr0 /peval.
    case: (p.[i] = zeror) => piP; rewrite ?piP.
    * suff -> : deg (take_poly 1 (drop_poly i p)) = 0 by rewrite range_geq.
      rewrite deg_eq0 poly_eqP; smt(coeffE coef_drop_poly ispolyTake poly0E).
    * have -> : deg (take_poly 1 (drop_poly i p)) = 1
        by apply degP; smt(coeffE coef_drop_poly ispolyTake).
      by smt(BigCf.BCA.big_seq1 coeffE coef_drop_poly
             expr0 ispolyTake mulr1 rangeS).
qed.

lemma rdvdp_XsubCl x p : rdvdp (polyX - polyC x) p = root p x.
proof.
have mond : lc (polyX - polyC x) = oner
  by rewrite lcDl ?lcX ?lcC // degN degC degX; case (_ = _).
by smt(PS.addr0 eq_rdvdp factor_theorem rdivp_eq).
qed.

end RingMonic.

abstract theory ComRing.

type coeff, poly.

clone ComRing as CR with type t <= coeff.

clone PolyComRing as PCR with
  type   coeff <= coeff,
  type   poly  <= poly,
  theory Coeff <- ComRing.CR.

clone ComRing.PCR.PolyComRing as PS.

clone RingPseudoDivision as RPD with
  type   coeff <= coeff,
  type   poly  <= poly,
  theory CR    <- ComRing.CR,
  theory PCR   <- ComRing.PCR,
  theory PS    <- ComRing.PS.

clone ComRegDivisor as CRD with
  type   coeff <= coeff,
  type   poly  <= poly,
  theory CR    <- ComRing.CR,
  theory PCR   <- ComRing.PCR,
  theory PS    <- ComRing.PS,
  theory RPD   <- ComRing.RPD.

clone RingMonic as RM with
  type   coeff <= coeff,
  type   poly  <= poly,
  theory CR    <- ComRing.CR,
  theory PCR   <- ComRing.PCR,
  theory PS    <- ComRing.PS,
  theory RPD   <- ComRing.RPD,
  theory CRD   <- ComRing.CRD.

import ComRing.CR.
import ComRing.PCR.
import ComRing.RPD.
import ComRing.CRD.
import ComRing.RM.

op redivp_spec (m d : poly) (i : int * poly * poly) =
  let (k, q, r) = i in
  exp (lc d) k ** m = q * d + r && (d <> poly0 => deg r < deg d).

lemma redivpP m d : redivp_spec m d (redivp m d)
  by smt(redivpP scalepE PS.mulrC).

lemma rdivp_eq d p :
  exp (lc d) (rscalp p d) ** p = rdivp p d * d + rmodp p d by smt(redivpP).

lemma rdvdp_eqP d p : rdvdp_spec p d (rmodp p d) (rdvdp d p).
proof.
case: (rdvdp d p) => [hdvd|/#]; move: (rmodp_eq0P p d); rewrite {2}hdvd.
move => _; rewrite /rdvdp_spec /=; exists (rscalp p d) (rdivp p d).
by rewrite rdivp_eq 1?PS.mulrC; smt(PS.addr0).
qed.

lemma rdvdp_eq q p :
  rdvdp q p = (exp (lc q) (rscalp p q) ** p = rdivp p q * q)
  by smt(PS.addr0 PS.addrI rdivp_eq).

(* Coeff.unit is a pred and not an op *)
op unit : coeff -> bool.

axiom unitP x : unit x = CR.unit x.

op diff_roots (x y : coeff) = unit (x - y).
  (* && x * y = y * x). *)

op uniq_roots (rs : coeff list) =
  with rs = []      => true
  with rs = c :: cs => all (diff_roots c) cs && uniq_roots cs.

lemma uniq_roots_prod_XsubC p rs :
  all (root p) rs => uniq_roots rs =>
  exists q, p = q * BigPoly.PCM.big predT (fun z => polyX - polyC z) rs.
proof.
elim rs; 1: by exists p; rewrite BigPoly.PCM.big_nil PS.mulr1.
move => z rs rsP [rpz rprs] [drs urs]; move: (rsP rprs urs) => {rsP} [q pqP].
move: (factor_theorem q z); suff -> : root q z.
- rewrite eq_sym eqT; move => [q' qq'P]; exists q'.
  by rewrite pqP qq'P; rewrite -PS.mulrA BigPoly.PCM.big_cons.
- move => {rprs urs}; move: drs rpz; rewrite pqP /=; move => {p pqP}.
  elim rs; 1: by rewrite BigPoly.PCM.big_nil PS.mulr1.
  move => t rs rsP /= [tzP urs].
  rewrite BigPoly.PCM.big_cons /predT /= -/predT PS.mulrCA pevalM.
  have: peval (X - polyC t) z = z - t by smt(pevalB pevalC pevalX).
  by smt(mulIr mulrC mul0r unitP).
qed.

lemma uniq_roots_rdvdp p rs :
  all (root p) rs => uniq_roots rs =>
  rdvdp (BigPoly.PCM.big predT (fun z => polyX - polyC z) rs) p.
proof.
move => har hur; move: (uniq_roots_prod_XsubC _ _ har hur) => [r ->].
pose qf := fun z => polyX - polyC z; pose q := BigPoly.PCM.big predT qf rs.
suff: lc q = oner by smt(rdvdp_mulr).
suff /# : forall rs, lc (BigPoly.PCM.big predT qf rs) = oner.
move => {rs har hur r q} rs; elim rs; 1: by rewrite BigPoly.PCM.big_nil lc1.
move => r rs rsh; rewrite BigPoly.PCM.big_cons.
suff: lc (qf r) = oner by smt(lcM_proper mulr1 oner_neq0).
by rewrite lcDl ?degN ?degC degX ?polyXE /#.
qed.

end ComRing.

abstract theory Idomain. (* Defs. *)

type coeff, poly.

clone IDomain as IDC with type t <= coeff.

clone Poly as P with
  type coeff         <= coeff,
  type poly          <= poly,
  theory IDCoeff     <- Idomain.IDC.

clone Idomain.P.IDPoly as PS.

clone RingPseudoDivision as RPD with
  type   coeff <= coeff,
  type   poly  <= poly,
  theory CR    <- Idomain.IDC,
  theory PCR   <- Idomain.P,
  theory PS    <- Idomain.PS.

clone ComRegDivisor as CRD with
  type   coeff <= coeff,
  type   poly  <= poly,
  theory CR    <- Idomain.IDC,
  theory PCR   <- Idomain.P,
  theory PS    <- Idomain.PS,
  theory RPD   <- Idomain.RPD.

clone RingMonic as RM with
  type   coeff <= coeff,
  type   poly  <= poly,
  theory CR    <- Idomain.IDC,
  theory PCR   <- Idomain.P,
  theory PS    <- Idomain.PS,
  theory RPD   <- Idomain.RPD,
  theory CRD   <- Idomain.CRD.

clone ComRing as CR with
  type   coeff <= coeff,
  type   poly  <= poly,
  theory CR    <- Idomain.IDC,
  theory PCR   <- Idomain.P,
  theory PS    <- Idomain.PS,
  theory RPD   <- Idomain.RPD,
  theory CRD   <- Idomain.CRD,
  theory RM    <- Idomain.RM.

import Idomain.IDC.
import Idomain.P.
import Idomain.RPD.
import Idomain.CRD.
import Idomain.RM.
import Idomain.CR.

op edivp (p q : poly) =
  let (k, d, r) = redivp p q in
  if ! unit (lc q) then (k, d, r) else
  let c = exp (lc q) (- k) in (0, c ** d, c ** r).

op divp p q = let (scal, div, mod) = edivp p q in div.
op modp p q = let (scal, div, mod) = edivp p q in mod.
op scalp p q = let (scal, div, mod) = edivp p q in scal.
op dvdp p q = (modp q p = poly0).
op eqp p q = (dvdp p q) && (dvdp q p).

lemma edivp_def p q : edivp p q = (scalp p q, divp p q, modp p q) by smt().

lemma edivp_redivp p q :
  ! CR.unit (lc q) => edivp p q = redivp p q by smt().

lemma divpE p q :
  divp p q = if CR.unit (lc q)
    then exp (lc q) (- rscalp p q) ** rdivp p q
    else rdivp p q by smt().

lemma modpE p q :
  modp p q = if CR.unit (lc q)
    then exp (lc q) (- rscalp p q) ** rmodp p q
    else rmodp p q by smt().

lemma scalpE p q :
  scalp p q = if CR.unit (lc q) then 0 else rscalp p q by smt().

lemma dvdpE p q : dvdp p q = rdvdp p q.
proof.
rewrite /dvdp modpE /rdvdp; case: (CR.unit (lc p)) => // lcU.
rewrite -!deg_eq0 degZ_lreg // lregP; smt(expf_eq0 CR.unitP unitr0).
qed.

lemma lc_expn_scalp_neq0 p q : exp (lc q) (scalp p q) <> zeror.
proof.
rewrite scalpE; case: (lc q = zeror) => qP; 2: by smt(expf_eq0).
have -> /= : ! CR.unit (lc q) by smt(CR.unitP unitr0).
have {qP} -> : q = poly0 by smt(lc_eq0).
by rewrite lc0 /rscalp /redivp /= expr0 oner_neq0.
qed.

op edivp_spec (m d : poly) (i : int * poly * poly) (b : bool) =
  let (k, q, r) = i in
  exp (lc d) k ** m = q * d + r && ! CR.unit (lc d) &&
  (d <> poly0 => deg r < deg d) && ! b ||
  m = q * d + r && CR.unit (lc d) &&
  (d <> poly0 => deg r < deg d) && k = 0 && b.

lemma edivpP m d : edivp_spec m d (edivp m d) (CR.unit (lc d)).
proof.
case: (CR.unit (lc d)) => lcP; 2: by smt(edivp_redivp redivpP).
have d_neq0 : d <> poly0 by smt(lc0 CR.unitP unitr0).
suff: m = divp m d * d + modp m d /\ deg (modp m d) < deg d by smt(scalpE).
rewrite divpE modpE lcP /=; split; 2: by smt(degZ_le ltn_rmodpN0).
rewrite scalepE -PS.mulrA- scalepE -scalepDr.
have: exp (lc d) (rscalp m d) ** m = rdivp m d * d + rmodp m d by smt(redivpP).
move => <-; rewrite scalepA mulrC -exprD -?CR.unitP //.
by rewrite subrr expr0 scalepE PS.mul1r.
qed.

lemma edivp_eq d q r :
  deg r < deg d => CR.unit (lc d) => edivp (q * d + r) d = (0, q, r).
proof.
move => hsrd hu; move: (Idomain.CRD.redivp_eq d q r).
have -> : injective (fun (x : coeff) => x * lc d) by smt(mulIr CR.unitP).
rewrite PS.mulrC hsrd /edivp hu /= => -> /=.
rewrite !scalepE PS.mulrCA -polyCM PS.mulrCA -polyCM.
by rewrite -exprD -?CR.unitP; smt(expr0 opprK subrr PS.mulr1).
qed.

lemma divp_eq p q : exp (lc q) (scalp p q) ** p = (divp p q) * q + (modp p q).
proof.
rewrite scalpE divpE modpE; case: (CR.unit (lc q)); 2: by rewrite rdivp_eq.
move => lcP; rewrite expr0 scalepE PS.mul1r scalepE -PS.mulrA.
rewrite -scalepE -scalepDr -rdivp_eq scalepA mulrC -exprD -?CR.unitP //.
by rewrite subrr expr0 scalepE PS.mul1r.
qed.

lemma dvdp_eq q p : dvdp q p = (exp (lc q) (scalp p q) ** p = (divp p q) * q).
proof.
rewrite dvdpE rdvdp_eq scalpE divpE; case: (CR.unit (lc q)) => // lcP.
rewrite expr0 eq_iff; split => [E|].
- rewrite scalepE PS.mul1r scalepE -PS.mulrA -E -scalepE.
  rewrite scalepA mulrC -exprD -?CR.unitP //.
  by rewrite subrr expr0 scalepE PS.mul1r.
- rewrite scalepE PS.mul1r => {2}->; rewrite !scalepE.
  rewrite !PS.mulrA -polyCM -exprD -?CR.unitP //.
  by rewrite subrr expr0 PS.mul1r.
qed.

lemma divpK d p : dvdp d p => divp p d * d = exp (lc d) (scalp p d) ** p
  by smt(dvdp_eq).

lemma divpKC d p : dvdp d p => d * (divp p d) = exp (lc d) (scalp p d) ** p
  by smt(divpK PS.mulrC).

lemma scalerAl (k : coeff) (x y : poly) : k ** (x * y) = k ** x * y
  by smt(PS.mulrA scalepE).

lemma scalerAr (k : coeff) (x y : poly) : k ** (x * y) = x * (k ** y)
  by smt(PS.mulrC scalerAl).

lemma dvdpP q p :
  (exists (c : coeff) (r : poly), c <> zeror /\ c ** p = r * q) = dvdp q p.
proof.
rewrite eqboolP iffE; split; 2: by smt(dvdp_eq lc_expn_scalp_neq0).
move => [c r] [c_neq0 pqP]; rewrite dvdpE.
case: (p = poly0) => [|p_neq0]; 1: by smt(rdvdp0).
have E : c ** rmodp p q = (exp (lc q) (rscalp p q) ** r - c ** (rdivp p q)) * q.
- rewrite PS.mulrDl PS.mulNr -scalerAl -pqP scalepA mulrC -scalepA -scalerAl.
  by rewrite -scalepBr rdivp_eq PS.addrC PS.addKr.
suff: (exp (lc q) (rscalp p q) ** r - c ** (rdivp p q)) * q = poly0
  by rewrite -E scalepE PS.mulf_eq0 eq_polyC0 /#.
smt(degM_proper degZ_lreg deg_gt0 lc_eq0 lregP ltn_rmodp mulf_eq0 PS.mulf_eq0).
qed.

lemma mulpK p q :
  q <> poly0 => divp (p * q) q = exp (lc q) (scalp (p * q) q) ** p.
proof.
move => q_neq0; apply (IDPoly.mulIf q); rewrite // scalepE -PS.mulrA.
rewrite -scalepE divp_eq; suff -> : modp (p * q) q = poly0
  by rewrite PS.addr0.
rewrite modpE Idomain.CRD.rmodp_mulr ?scalep0 1?PS.mulrC //.
by rewrite mulIf lc_eq0.
qed.

lemma mulKp p q :
  q <> poly0 => divp (q * p) q = exp (lc q) (scalp (p * q) q) ** p
  by smt(PS.mulrC mulpK).

lemma divpp p : p <> poly0 => divp p p = polyC (exp (lc p) (scalp p p)).
proof.
move => p_neq0; have := divp_eq p p.
suff -> : modp p p = poly0
   by rewrite PS.addr0 scalepE; smt(IDPoly.mulIf).
by rewrite modpE Idomain.RPD.rmodpp ?scalep0 // PS.mulrC.
qed.

lemma scalp0 p : scalp p poly0 = 0
  by rewrite /scalp /edivp /redivp lc0 CR.unitP unitr0.

lemma divp_small p q : deg p < deg q => divp p q = poly0
  by move => spq; rewrite divpE rdivp_small // scalep0.

lemma leq_divp p q : deg (divp p q) <= deg p by smt(degZ_le divpE leq_rdivp).

lemma div0p p : divp poly0 p = poly0 by rewrite divpE rdiv0p scalep0.

lemma divp0 p : divp p poly0 = poly0  by rewrite divpE rdivp0 scalep0.

lemma divp1 m : divp m poly1 = m
  by rewrite divpE rdivp1 lc1 expr1z scalepE PS.mul1r.

lemma modp0 p : modp p poly0 = p by rewrite modpE rmodp0 lc0 CR.unitP unitr0.

lemma mod0p p : modp poly0 p = poly0 by rewrite modpE rmod0p scalep0.

lemma modp1 p : modp p poly1 = poly0 by rewrite modpE rmodp1 scalep0.

lemma modp_small p q : deg p < deg q => modp p q = p.
proof.
move => spq; rewrite modpE rmodp_small //; case: (CR.unit (lc q)) => // lcP.
by rewrite rscalp_small // oppr0 expr0 scalepE PS.mul1r.
qed.

lemma modpC p c : c <> zeror => modp p (polyC c) = poly0
  by move => c_neq0; rewrite modpE rmodpC // scalep0.

lemma neq0_rreg p : p <> poly0 => injective (fun (x : coeff) => x * lc p)
  by move => p_neq0 y z; rewrite -subr_eq0 -mulrBl mulf_eq0 subr_eq0 lc_eq0 /#.

lemma modp_mull (p q : poly) : modp (p * q) q = poly0.
proof.
case: (q = poly0) => [|q_neq0]; 1: by smt(mod0p PS.mulr0).
rewrite modpE Idomain.CRD.rmodp_mulr;
by rewrite ?scalep0 1?PS.mulrC // neq0_rreg.
qed.

lemma modp_mulr (d p : poly) : modp (d * p) d = poly0
  by rewrite PS.mulrC modp_mull.

lemma modpp d : modp d d = poly0 by smt(PS.mul1r modp_mull).

lemma ltn_modp p q : (deg (modp p q) < deg q) = (q <> poly0).
proof.
rewrite modpE; case: (CR.unit (lc q)) => lcP; 2: by smt(ltn_rmodp).
by rewrite degZ_lreg ?ltn_rmodp // lregP expf_eq0; smt(CR.unitP unitr0).
qed.

lemma ltn_divpl d q p :
  d <> poly0 => (deg (divp q d) < deg p) = (deg q < deg (p * d)).
proof.
move => d_neq0; rewrite -(degZ_lreg (exp (lc d) (scalp q d)) q);
rewrite ?lregP ?lc_expn_scalp_neq0 // divp_eq.
case: (divp q d = poly0) => [->|div_qd_neq0].
- rewrite deg0 deg_gt0 PS.mul0r PS.add0r.
  case: (p = poly0) => [->|p_neq0];
    1: by rewrite PS.mul0r deg0; smt(ge0_deg).
  rewrite /= eq_sym eqT degM_proper; 2: by smt(deg_gt0 ltn_modp).
  by rewrite mulf_eq0 !lc_eq0 p_neq0 d_neq0.
- rewrite degDl; 1: by smt(degM_proper deg_gt0 lc_eq0 ltn_modp mulf_eq0).
  case: (p = poly0) => [->|];
    1: by smt(deg0 deg_gt0 PS.mul0r IDPoly.mulf_eq0).
  by move => p_neq0; rewrite !degM_proper ?mulf_eq0 ?lc_eq0 /#.
qed.

lemma leq_divpr d p q :
  d <> poly0 => (deg p <= deg (divp q d)) = (deg (p * d) <= deg q)
  by smt(ler_gtF ltn_divpl).

lemma divpN0 d p : d <> poly0 => (divp p d <> poly0) = (deg d <= deg p)
  by move => d_neq0; rewrite -{2}(PS.mul1r d) -leq_divpr;
     smt(deg1 deg_gt0).

lemma size_divp p q :
  q <> poly0 => deg (divp p q) = max 0 (deg p - (deg q - 1)).
proof.
move => q_neq0; case: (deg p < deg q) => dpq; 1: by smt(deg0 divp_small).
have {dpq} dpq : deg q <= deg p by smt().
have p_neq0 : p <> poly0 by smt(deg_gt0).
move: (congr1 deg _ _ (divp_eq p q)).
rewrite degZ_lreg ?lregP ?lc_expn_scalp_neq0 //.
case: (divp p q = poly0);
  1: by smt(PS.add0r deg0 ltn_modp PS.mul0r).
move => dpq_neq0; rewrite degDl; 2: by smt(degM_proper ge0_deg lc_eq0 mulf_eq0).
by rewrite degM_proper; smt(deg_gt0 lc_eq0 ltn_modp mulf_eq0).
qed.

lemma ltn_modpN0 p q : q <> poly0 => deg (modp p q) < deg q by rewrite ltn_modp.

lemma modp_mod p q : modp (modp p q) q = modp p q
  by smt(ltn_modp modp0 modp_small).

lemma leq_modp m d : deg (modp m d) <= deg m by smt(degZ_le leq_rmodp modpE).

lemma dvdp0 d : dvdp d poly0 by rewrite /dvdp mod0p.

lemma dvd0p p : (dvdp poly0 p) = (p = poly0) by rewrite /dvdp modp0.

(* skip? *)
lemma dvd0pP p : (p = poly0) = dvdp poly0 p by smt(dvd0p).

lemma dvdpN0 p q : dvdp p q => q <> poly0 => p <> poly0 by smt(dvd0p).

lemma dvdp1 d : dvdp d poly1 = (deg d = 1).
proof.
rewrite /dvdp modpE; case: (CR.unit (lc d)) => lcP; 2: by smt(rdvdp1).
rewrite -deg_eq0 degZ_lreg ?deg_eq0 -?rdvdp1 // lregP.
by rewrite -invr_eq0 -exprN opprK; smt(expf_eq0 CR.unitP unitr0).
qed.

lemma dvd1p m : dvdp poly1 m by rewrite /dvdp modp1.

lemma gtNdvdp p q : p <> poly0 => deg p < deg q => dvdp q p = false
  by smt(modp_small).

(* skip? *)
lemma modp_eq0P p q : (modp p q = poly0) = dvdp q p by [].

lemma modp_eq0 p q : dvdp q p => modp p q = poly0 by [].

lemma leq_divpl d p q :
  dvdp d p => deg (divp p d) <= deg q = deg p <= deg (q * d).
proof.
case: (d = poly0) => [->|d_neq0]; 1: by rewrite dvd0p divp0; smt(deg0 ge0_deg).
move => ddp; rewrite ler_eqVlt ltn_divpl // (ler_eqVlt (deg p)).
case: (deg p < deg (q * d)) => //= lhs.
rewrite -(degZ_lreg (exp (lc d) (scalp p d)) p) ?lregP ?lc_expn_scalp_neq0 //.
rewrite divp_eq (modp_eq0 _ _ ddp) PS.addr0.
case: (divp p d = poly0) => [->|];
  1: by smt(deg_eq0 IDPoly.mulf_eq0 PS.mul0r).
case: (q = poly0) => 2?; 1: by smt(deg_eq0 IDPoly.mulf_eq0 PS.mul0r).
by rewrite !degM_proper; smt(lc_eq0 mulf_eq0).
qed.

lemma dvdp_leq p q : q <> poly0 => dvdp p q => deg p <= deg q
  by smt(modp_eq0 modp_small).

lemma eq_dvdp c (quo q p : poly) : c <> zeror => c ** p = quo * q => dvdp q p.
proof.
move => c_neq0; case: (p = poly0) => [|p_neq0 def_quo]; 1: by smt(dvdp0).
pose p1 := exp (lc q) (scalp p q) ** quo - c ** divp p q.
have E1 : c ** modp p q = p1 * q.
- rewrite PS.mulrBl (scalepE _ quo) -PS.mulrA -scalepE.
  rewrite -def_quo scalepA mulrC -scalepA divp_eq -PS.subr_eq.
  rewrite PS.opprK PS.addrC.
  by rewrite scalepE -PS.mulrA -scalepE scalepDr.
apply contraT; rewrite /dvdp => m_neq0.
have: p1 * q <> poly0 by rewrite -E1 scalepE IDPoly.mulf_eq0 eq_polyC0 /#.
rewrite IDPoly.mulf_eq0 negb_or; move => [p1_neq0 q_neq0].
move: (ltn_modp p q); rewrite q_neq0 -(degZ_lreg c) ?lregP // E1.
by smt(degM_proper deg_gt0 mulf_eq0 lc_eq0).
qed.

lemma dvdpp d : dvdp d d by rewrite /dvdp modpp.

lemma divp_dvd p q : dvdp p q => dvdp (divp q p) q
  by smt(dvdp_eq eq_dvdp expf_eq0 lc_eq0 PS.mulrC).

lemma dvdp_mulr m d n : dvdp d n => dvdp d (m * n).
proof.
case: (d = poly0) => [|d_neq0 e]; 1: by smt(dvd0p PS.mulr0).
move: (eq_dvdp (exp (lc d) (scalp n d)) (m * divp n d)).
by smt(dvdp_eq expf_eq0 lc_eq0 PS.mulrA scalerAr).
qed.

lemma dvdp_mull n d m : dvdp d m => dvdp d (m * n)
  by move => dmP; rewrite PS.mulrC dvdp_mulr.

lemma dvdp_mul d1 d2 m1 m2 :
  dvdp d1 m1 => dvdp d2 m2 => dvdp (d1 * d2) (m1 * m2).
proof.
case: (d1 = poly0) => [|d1_neq0]; 1: by smt(dvd0p PS.mul0r).
case: (d2 = poly0) => [|d2_neq0]; 1: by smt(dvd0p PS.mulr0).
move: (eq_dvdp ((exp (lc d1) (scalp m1 d1)) * (exp (lc d2) (scalp m2 d2)))
               (divp m1 d1 * divp m2 d2)).
by smt(dvdp_eq expf_eq0 lc_eq0 mulf_eq0 PS.mulrA
       PS.mulrC scalepA scalerAl scalerAr).
qed.

lemma dvdp_addr m d n : dvdp d m => dvdp d (m + n) = dvdp d n.
proof.
case: (d = poly0) => [|d_neq0]; 1: by smt(dvd0p PS.add0r).
rewrite dvdp_eq eqboolP iffE {1}dvdp_eq {2}dvdp_eq => e1; split => e2.
- apply: (eq_dvdp (exp (lc d) (scalp m d) * exp (lc d) (scalp (m + n) d))
                  (exp (lc d) (scalp m       d) ** divp (m + n) d -
                   exp (lc d) (scalp (m + n) d) ** divp m       d));
    1: by smt(mulf_eq0 expf_eq0 lc_eq0).
  rewrite PS.mulrDl -scaleNp -!scalerAl -e1 -e2 !scalepA mulNr mulrC.
  rewrite scaleNp -scalepBr PS.addrAC.
  by rewrite PS.subrr PS.add0r.
- apply: (eq_dvdp (exp (lc d) (scalp m d) * exp (lc d) (scalp n d))
                  (exp (lc d) (scalp m d) ** divp n d +
                   exp (lc d) (scalp n d) ** divp m d));
    1: by smt(mulf_eq0 expf_eq0 lc_eq0).
  rewrite PS.mulrDl -!scalerAl -e1 -e2 !scalepA.
  by rewrite mulrC PS.addrC scalepDr.
qed.

lemma dvdp_addl n d m : dvdp d n => dvdp d (m + n) = dvdp d m
  by smt(PS.addrC dvdp_addr).

lemma dvdp_add d m n : dvdp d m => dvdp d n => dvdp d (m + n) by smt(dvdp_addr).

lemma dvdp_add_eq (d m n : poly) : dvdp d (m + n) => dvdp d m = dvdp d n
  by smt(dvdp_addl dvdp_addr).

lemma dvdp_subr d m n : dvdp d m => dvdp d (m - n) = dvdp d n
  by move=> ?; apply: dvdp_add_eq; rewrite -PS.addrA;
     rewrite PS.addNr PS.addr0.

lemma dvdp_subl d m n : dvdp d n => dvdp d (m - n) = dvdp d m
  by move => dnP; rewrite -(dvdp_addl n d (m - n)) // PS.subrK.

lemma dvdp_sub d m n : dvdp d m => dvdp d n => dvdp d (m - n)
  by move => *; rewrite dvdp_subl.

lemma dvdp_mod d n m : dvdp d n => dvdp d m = dvdp d (modp m n).
proof.
case: (n = poly0) => [|n_neq0]; 1: by smt(modp0).
case: (d = poly0) => [|d_neq0]; 1: by smt(modp0).
rewrite dvdp_eq eqboolP iffE {1}dvdp_eq {2}dvdp_eq => e1; split => e2.
- apply: (eq_dvdp (exp (lc d) (scalp n d) * exp (lc d) (scalp m d))
                  ((exp (lc d) (scalp n d) *
                    exp (lc n)  (scalp m n)) ** divp m d -
                   exp (lc d) (scalp m d) ** divp m n * divp n d));
    1: by smt(expf_eq0 lc_eq0 mulf_eq0).
  rewrite PS.mulrDl PS.mulNr -!scalerAl -PS.mulrA.
  rewrite -e1 -e2 -scalerAr  scalepA mulrC -mulrA.
  rewrite (mulrC (exp (lc n) (scalp m n))) mulrCA mulrA -!scalepA.
  by rewrite divp_eq !scalepA -scalepBr PS.addrC PS.addKr.
- apply: (eq_dvdp (exp (lc d) (scalp n d) * exp (lc d) (scalp (modp m n) d) *
                   exp (lc n) (scalp m n))
                  (exp (lc d) (scalp (modp m n) d) ** divp m n * divp n d +
                   exp (lc d) (scalp n d) ** divp (modp m n) d));
    1: by smt(expf_eq0 lc_eq0 mulf_eq0).
  rewrite -scalepA divp_eq scalepDr -!scalepA e2 scalerAl scalerAr e1.
  by rewrite scalerAl PS.mulrDl PS.mulrA.
qed.

lemma dvdp_trans : transitive dvdp.
proof.
move => n d m; case: (d = poly0); case: (n = poly0); 1..3: by smt(dvd0p).
rewrite 2!dvdp_eq => n_neq0 d_neq0 e1 e2.
apply: (eq_dvdp (exp (lc d) (scalp n d) * exp (lc n) (scalp m n))
                (divp n d * divp m n)); 1: by smt(expf_eq0 lc_eq0 mulf_eq0).
by rewrite -scalepA e2 scalerAr e1 PS.mulrCA PS.mulrA.
qed.

lemma dvdp_mulIl (p q : poly) : dvdp p (p * q) by smt(dvdpp dvdp_mull).

lemma dvdp_mulIr (p q : poly) : dvdp q (p * q) by smt(dvdpp dvdp_mulr).

lemma dvdp_mul2r r p q : r <> poly0 => dvdp (p * r) (q * r) = dvdp p q.
proof.
case: (p = poly0) => [|p_neq0 r_neq0]; 1: by smt(dvd0p IDPoly.mulf_eq0).
case: (q = poly0) => [|q_neq0]; 1: by smt(dvdp0 PS.mul0r).
rewrite eqboolP iffE; split; 2: by move => ?; rewrite dvdp_mul ?dvdpp.
rewrite dvdp_eq => e.
apply: (eq_dvdp (exp (lc (p * r)) (scalp (q * r) (p * r)))
                (divp (q * r) (p * r))); 1: by smt(expf_eq0 lc_eq0 mulf_eq0).
by smt(IDPoly.mulIf PS.mulrA scalerAl).
qed.

lemma dvdp_mul2l r p q: r <> poly0 => dvdp (r * p) (r * q) = dvdp p q
  by smt(dvdp_mul2r PS.mulrC).

lemma ltn_divpr d p q :
  dvdp d q => deg p < deg (divp q d) = (deg (p * d) < deg q)
  by smt(ler_eqVlt leq_divpl).

lemma dvdp_exp d k p : 0 < k => dvdp d p => dvdp d (PS.exp p k).
proof.
move: k d p; apply: natind => [/#|k k_ge0 kP d p _].
case: (k = 0) => [->|k_neq0]; 1: by rewrite PS.expr1.
have {k_ge0 k_neq0} k_gt0 : 0 < k by smt().
by smt(dvdp_mulr PS.exprSr).
qed.

(* 0 <= k is required
   take k to be - (oner + oner), l be oner and p be X
   then k <= l is true but PS.exp d k = polyXn 2 and PS.exp d l = X
   so deg (PS.exp d l) < deg (PS.exp d k) and from gtNdvdp we get
   ! dvdp (PS.exp d k) (PS.exp d l) *)
lemma dvdp_exp2l d (k l : int) :
  0 <= k <= l => dvdp (PS.exp d k) (PS.exp d l).
proof.
move => klP; have -> : l = l - k + k by rewrite addrAC -addrA subrr addr0.
by rewrite PS.exprD_nneg ?dvdp_mulr ?dvdpp /#.
qed.

lemma degXn_proper (p : poly) i :
  lreg (lc p) => 0 <= i => deg (PS.exp p i) = i * (deg p - 1) + 1.
proof.
move=> lreg_p; elim: i => [|i ge0_i ih]; first by rewrite PS.expr0 deg1.
rewrite PS.exprS // degM_proper; last by rewrite ih #ring.
by rewrite mulrI_eq0 // lc_eq0 PS.expf_eq0 -lc_eq0; smt(lregP).
qed.

(* 0 <= k and 0 <= l are required
   take k to be - (oner + oner), l be - oner and p be X
   then k <= l is true but PS.exp d k = polyXn 2 and PS.exp d l = X
   so deg (PS.exp d l) < deg (PS.exp d k) and from gtNdvdp we get
   ! dvdp (PS.exp d k) (PS.exp d l)
   similarly the statement is wrong when k is oner, l is - oner and p is X
   indeed ! k <= l but dvdp (PS.exp d k) (PS.exp d l) = dvdp X X = true (dvdpp),
   or when k is - (oner + oner), l is oner and p is X
   indeed k <= l but dvdp (PS.exp d k) (PS.exp d l) = dvdp (polyXn 2) X = false
   since 2 = deg X < deg (polyXn 2) = 3 (gtNdvdp) *)
lemma dvdp_Pexp2l d k l :
  0 <= k => 0 <= l => 1 < deg d =>
  dvdp (PS.exp d k) (PS.exp d l) = (k <= l).
proof.
case: (k <= l) => [|klP k_ge0 l_ge0 dP]; 1: by smt(dvdp_exp2l).
have d_neq0 : d <> poly0 by smt(deg_ge1).
rewrite gtNdvdp ?PS.expf_eq0 ?d_neq0; 1, 3: by smt(PS.expf_eq0).
by rewrite !degXn_proper ?lregP ?lc_eq0 /#.
qed.

(* provable even k is negative *)
lemma dvdp_exp2r p q k :
  dvdp p q => dvdp (PS.exp p k) (PS.exp q k).
proof.
case: (p = poly0) => [|p_neq0]; 1: by smt(dvdpp dvd0p PS.expr0z).
case: (q = poly0) => [|q_neq0]; 1: by smt(dvdp0 dvd1p PS.expr0 PS.expr0z).
wlog: k / 0 <= k => [kP|k_ge0].
- case: (0 <= k) => [/#|k_nge0 pqP].
  have [k' [k'_ge0 ->]] {k k_nge0} : exists k', 0 <= k' /\ k = -k' by smt().
  case: (deg p = 1); 1: smt(degC degV deg_eq1 expf_eq0 PS.exprV modpC polyCX).
  move => pP; have pnu: ! (PS.unit p) by smt().
  have qnu : ! PS.unit q by smt(deg_eq0 dvdp_leq ge0_deg).
  by rewrite -!PS.exprV !PS.invr_out /#.
- rewrite dvdp_eq => e.
  apply: (eq_dvdp (exp (exp (lc p) (scalp q p)) k) (PS.exp (divp q p) k));
    1: by smt(expf_eq0 lc_eq0 mulf_eq0).
  by rewrite -PS.exprMn // -e (scalepE _ q) PS.exprMn // polyCX // -scalepE.
qed.

(* 0 <= k - l and 0 <= l are required
   take k to be oner, l be oner + oner, p be X and q be poly1,
   here 0 <= l but ! 0 <= k - l and
   then PS.exp d k = X, PS.exp d l = polyXn 2 and PS.exp p (k - l) = X
   so since q = poly1 but deg (PS.exp p (k - l)) = 2
   then ! dvdp (PS.exp p (k - l)) q from dvdp1
   but PS.exp p k = X and q * (PS.exp p l) = X * X so
   dvdp (PS.exp p k) (q * (PS.exp p l)) from dvdp_mulIl
   similarly the statement is wrong when
   k is - oner, l is - (oner + oner), p is X and q is poly1,
   here 0 <= k - l but ! 0 <= l and
   indeed ! dvdp (PS.exp p (k - l)) q from dvdp1 as
   q = poly1 but deg (PS.exp p (k - l)) = 2
   but PS.exp p k = X and q * (PS.exp p l) = X * X so
   dvdp (PS.exp p k) (q * (PS.exp p l)) from dvdp_mulIl,
   or when k is - oner, l is - (oner + oner), p is X and q is poly1,
   here ! 0 <= k - l as well as ! 0 <= l and
   indeed  ! dvdp (PS.exp p (k - l)) q from dvdp1 as
   q = poly1 but deg (PS.exp p (k - l)) = 2
   but PS.exp p k = X and q * (PS.exp p l) = X * X so
   dvdp (PS.exp p k) (q * (PS.exp p l)) from dvdp_mulIl
*)
lemma dvdp_exp_sub p q (k l : int) :
  0 <= k - l => 0 <= l => p <> poly0 =>
  dvdp (PS.exp p k) (q * (PS.exp p l)) = dvdp (PS.exp p (k - l)) q.
proof.
have {2}-> klP lP p_neq0 : k = k - l + l by smt().
by rewrite PS.exprD_nneg // dvdp_mul2r // PS.expf_eq0 p_neq0.
qed.

lemma dvdp_XsubCl p x : dvdp (polyX - polyC x) p = root p x
  by rewrite dvdpE rdvdp_XsubCl.

(* skip? *)
lemma polyXsubCP p x : (peval p x = zeror) = dvdp (polyX - polyC x) p
  by smt(dvdp_XsubCl).

lemma eqp_div_XsubC p c :
  (p = divp p (polyX - polyC c) * (polyX - polyC c)) = dvdp (polyX - polyC c) p
  by rewrite dvdp_eq lcDl; smt(degC degN degX expr1z PS.mul1r lcX scalepE).

lemma root_factor_theorem p x : root p x = dvdp (polyX - polyC x) p
  by rewrite dvdp_XsubCl.

lemma uniq_roots_dvdp p rs :
  all (root p) rs => uniq_roots rs =>
  dvdp (BigPoly.PCM.big predT (fun z => polyX - polyC z) rs) p.
proof.
move => rrs urs; move: (uniq_roots_prod_XsubC _ _ rrs urs) => [q ->].
by rewrite dvdp_mulr dvdpp.
qed.

lemma root_bigmul x ps :
  ! root (BigPoly.PCM.big predT idfun ps) x = all (fun p => ! root p x) ps.
proof.
elim ps => [|p ps ihp]; 1: by rewrite BigPoly.PCM.big_nil root1.
by rewrite BigPoly.PCM.big_cons /predT /= rootM /#.
qed.

lemma eqpP m n :
  (exists c1 c2, c1 <> zeror && c2 <> zeror && c1 ** m = c2 ** n) =
  (eqp m n).
proof.
rewrite eqboolP iffE; split; 1: by smt(eq_dvdp scalepE).
case: (m = poly0) => [|m_neq0]; 1: by smt(dvd0p oner_neq0 scalep0).
case: (n = poly0) => [|n_neq0]; 1: by smt(dvd0p oner_neq0 scalep0).
rewrite /eqp !dvdp_eq; move => [e1 e2].
have c1_neq0 : exp (lc m) (scalp n m) <> zeror by smt(expf_eq0 lc_eq0 mulf_eq0).
have c2_neq0 : exp (lc n) (scalp m n) <> zeror by smt(expf_eq0 lc_eq0 mulf_eq0).
have def_q12 : divp n m * divp m n = polyC (exp (lc m) (scalp n m) *
                                            exp (lc n) (scalp m n)).
- apply: (PS.mulIf m); rewrite // PS.mulrAC PS.mulrC -e1 -scalerAr -e2.
  by rewrite scalepA scalepE.
have: divp n m * divp m n <> poly0 by rewrite def_q12 eq_polyC0 mulf_eq0 /#.
rewrite PS.mulf_eq0 negb_or; move => [q1_neq0 q2_neq0].
have q2P : deg (divp m n) <= 1.
- move: (degM_proper (divp n m) (divp m n)); rewrite mulf_eq0 !lc_eq0.
  rewrite q1_neq0 q2_neq0 /= def_q12 degC mulf_eq0 c1_neq0 c2_neq0.
  by rewrite -addrA addrCA; smt(deg_gt0 ler_addl).
have {q2P} : deg (divp m n) = 1 by smt(deg_gt0).
rewrite deg_eq1; move => [c [c_neq0 cq2e]]; exists (exp (lc n) (scalp m n)) c.
by rewrite c2_neq0 c_neq0 /= e2 scalepE -cq2e.
qed.

lemma eqp_eq p q: eqp p q => (lc q) ** p = (lc p) ** q.
proof.
rewrite -eqpP; move => [c1 c2] [c1_neq0 [c2_neq0 e]].
move: (congr1 lc _ _ e); rewrite /= !lcZ_lreg ?lregP // => eqC.
by apply: (PS.mulfI (polyC c2)); rewrite ?eq_polyC0; smt(mulrC scalepA scalepE).
qed.

lemma eqpxx : reflexive eqp by smt(dvdpp).

lemma eqp_sym : symmetric eqp by smt().

lemma eqp_trans : transitive eqp by smt(dvdp_trans).

lemma eqp_ltrans : left_transitive eqp by smt(eqp_sym eqp_trans).

lemma eqp_rtrans : right_transitive eqp by smt(eqp_sym eqp_trans).

lemma eqp0 p : eqp p poly0 = (p = poly0) by smt(dvd0p).

lemma eqp01 : eqp poly0 poly1 = false by rewrite eqp_sym eqp0 PS.oner_neq0.

lemma eqp_scale p c : c <> zeror => eqp (c ** p) p.
proof.
move => c_neq0; rewrite -eqpP; exists oner c; rewrite c_neq0 oner_neq0 /=.
by rewrite scalepE PS.mul1r.
qed.

lemma eqp_size p q : eqp p q => deg p = deg q
  by smt(deg0 dvdp_leq eqp0 eqp_sym ler_anti).

lemma size_poly_eq1 p : (deg p = 1) = eqp p poly1 by smt(dvdp1 dvd1p).

lemma polyXsubC_eqp1 x : eqp (polyX - polyC x) poly1 = false
  by rewrite -size_poly_eq1 degNXC.

lemma dvdp_eqp1 p q : dvdp p q => eqp q poly1 => eqp p poly1
  by smt(deg_gt0 dvd0p dvdp_leq size_poly_eq1).

lemma eqp_dvdr q p d: eqp p q => dvdp d p = dvdp d q by smt(eqp_sym dvdp_trans).

lemma eqp_dvdl d2 d1 p : eqp d1 d2 => dvdp d1 p = dvdp d2 p
  by smt(eqp_sym dvdp_trans).

lemma dvdpZr c m n : c <> zeror => dvdp m (c ** n) = dvdp m n
  by smt(eqp_dvdr eqp_scale).

lemma dvdpZl c m n : c <> zeror => dvdp (c ** m) n = dvdp m n
  by smt(eqp_dvdl eqp_scale).

lemma scale1r : left_id oner polyZ by smt(PS.mul1r scalepE).

lemma scaleN1r p : (- oner) ** p = - p by smt(scaleNp scale1r).

lemma dvdpNl (d p : poly) : dvdp (- d) p = dvdp d p
  by rewrite -scaleN1r; apply/eqp_dvdl/eqp_scale; rewrite oppr_eq0 oner_neq0.

lemma dvdpNr (d p : poly) : dvdp d (- p) = dvdp d p
  by apply: eqp_dvdr; rewrite -scaleN1r eqp_scale oppr_eq0 oner_neq0.

lemma eqp_mul2r r p q : r <> poly0 => eqp (p * r) (q * r) = eqp p q
  by smt(dvdp_mul2r).

lemma eqp_mul2l r p q: r <> poly0 => eqp (r * p) (r * q) = eqp p q
  by smt(dvdp_mul2l).

lemma eqp_mull r p q: eqp q r => eqp (p * q) (p * r) by smt(eqpP scalerAr).

lemma eqp_mulr q p r : eqp p q => eqp (p * r) (q * r) by smt(eqp_mull PS.mulrC).

lemma eqp_mul p q r s : eqp p q => eqp r s => eqp (p * r) (q * s).
proof. by move/(eqp_mulr _ _ r) => + /(eqp_mull _ q); apply/eqp_trans. qed.

lemma eqp_prod ['a] P F G (s : 'a list) :
  all (fun x => P x => eqp (F x) (G x)) s =>
  eqp (BigPoly.PCM.big P F s) (BigPoly.PCM.big P G s).
proof.
elim: s => [|x s IHs].
+ by rewrite !BigPoly.PCM.big_nil /=; apply/eqpxx.
rewrite !BigPoly.PCM.big_cons /= => -[] + /IHs eqp__.
by case (P x) => //= Px eqp_; apply/eqp_mul.
qed.

lemma eqp_exp p q k : eqp p q => eqp (PS.exp p k) (PS.exp q k).
proof.
move: k; apply: natind => /= [n n_le0|n n_ge0 nh pqP]; rewrite ?PS.exprS //;
  2: by apply: (eqp_trans (q * PS.exp p n)); smt(eqpxx eqp_mull eqp_mulr).
have [m [m_ge0 ->]] {n n_le0} : exists m, 0 <= m /\ n = -m by smt().
move: m m_ge0; apply: natind => /= [|n n_ge0 nh _]; 1: by smt(eqpxx PS.expr0).
move => pqP; move: (nh n_ge0 pqP); rewrite -!PS.exprV !PS.exprS // => {nh} nh.
suff pqVP: eqp (polyV p) (polyV q)
  by apply: (eqp_trans (polyV q * PS.exp (polyV p) n));
     smt(eqpxx eqp_mull eqp_mulr).
suff: forall p q, unitp p => eqp p q => eqp (polyV p) (polyV q)
  by smt(eqp_sym PS.invr_out).
move => {p q n n_ge0 pqP nh} p q pP pqP; rewrite /polyV.
have [dp dq] /= : deg p = 1 /\ deg q = 1 by smt(eqp_size).
move: (deg_eq1 p) (deg_eq1 q); rewrite dp dq /=.
move => [cp [cp_neq0 cpP]] [cq [cq_neq0 cqP]].
rewrite cpP cqP !polyCE /=; pose c := cp / cq.
suff: c <> zeror /\ polyC (invr cq) = c ** polyC (invr cp) by smt(eqp_scale).
rewrite /c mulf_eq0 cp_neq0 invr_neq0 //=.
by rewrite scalepE polyCM PS.mulrAC -polyCM divrr ?PS.mul1r; smt(polyCE).
qed.

lemma polyC_eqp1 c : eqp (polyC c) poly1 = (c <> zeror)
  by rewrite /eqp dvd1p /= dvdp1 degC /#.

lemma dvdUp d p: eqp d poly1 => dvdp d p by smt(dvd1p eqp_dvdl).

lemma dvdp_size_eqp p q : dvdp p q => (deg p = deg q) = eqp p q.
proof.
move => pqP; rewrite eqboolP iffE; split; 2: by exact: eqp_size.
case: (p = poly0) => [|p_neq0]; 1: by smt(deg_eq0).
case: (q = poly0) => [|q_neq0]; 1: by smt(deg_eq0).
move: pqP; rewrite dvdp_eq => e.
have c_neq0 : exp (lc p) (scalp q p) <> zeror by smt(expf_eq0 mulf_eq0 lc_eq0).
move: (congr1 deg _ _ e); rewrite degZ_lreg ?lregP //.
rewrite degM; 1, 2: by smt(eq_polyC0 PS.mulf_eq0 PS.mul0r scalepE).
rewrite -eqpP; move => eC pqP; have {eC} : deg (divp q p) = 1 by smt().
rewrite deg_eq1; move => [y [y_neq0 yP]]; exists y (exp (lc p) (scalp q p)).
by rewrite c_neq0 y_neq0 /= e yP scalepE.
qed.

lemma eqp_root p q : eqp p q => root p = root q.
proof.
rewrite -eqpP; move => [c1 c2] [c1nz [c2nz cP]].
suff /# : forall x, (false \/ root p x) = (false \/ root q x).
have [{2}-> ->] : false = (c1 = zeror) /\ false = (c2 = zeror) by smt().
by move => x; rewrite -mulf_eq0 -P.pevalZ cP P.pevalZ mulf_eq0.
qed.

lemma eqp_rmod_mod p q : eqp (rmodp p q) (modp p q)
  by smt(eqpxx eqp_scale eqp_sym expf_eq0 modpE unitP unitr0).

lemma eqp_rdiv_div p q : eqp (rdivp p q) (divp p q)
  by smt(divpE eqpxx eqp_scale eqp_sym expf_eq0 unitP unitr0).

lemma dvd_eqp_divl d p q :
  dvdp d q => eqp p q => eqp (divp p d) (divp q d)
  by smt(divpK dvd0p eqp0 eqpxx eqp_dvdr eqp_ltrans
         eqp_mul2r eqp_scale lc_expn_scalp_neq0).

(* It will go through useless loops once "r = poly0"
   since iter is needed as recursive calls are currently not allowed. *)
op gcdp_rec_it (i : poly * poly) =
  let (p, q) = i in
  let r = modp p q in
  if r = poly0 then i else (q, r).

(* nosimpl useful? *)
op gcdp (p q : poly) =
  let (pp, qq) = if deg p < deg q then (q, p) else (p, q) in
  if pp = poly0 then qq else
  let (ppp, qqq) = iter (deg pp) gcdp_rec_it (pp, qq) in qqq.

lemma gcd0p : left_id poly0 gcdp.
proof.
move => p; rewrite /gcdp /gcdp_rec_it /= deg0 deg_gt0.
case: (p = poly0) => //= p_neq0; rewrite p_neq0 /=.
have [n [-> n_ge0]] : exists n, deg p = n + 1 /\ 0 <= n by smt(deg_gt0).
by rewrite iterSr // iter_id /= modp0 p_neq0 /= ?mod0p.
qed.

lemma gcdp0 : right_id poly0 gcdp.
proof.
move => p; rewrite /gcdp /gcdp_rec_it deg0; have: ! deg p < 0 by smt(ge0_deg).
case: (p = poly0) => // p_neq0 -> /=.
have [n [-> n_ge0]] : exists n, deg p = n + 1 /\ 0 <= n by smt(deg_gt0).
by rewrite p_neq0 /= iterSr // iter_id /= modp0 p_neq0 /= ?mod0p.
qed.

lemma gcdpE p q :
  gcdp p q = if deg p < deg q
    then gcdp (modp q p) p else gcdp (modp p q) q.
proof.
have Irec : forall k l i, deg (snd i) <= k => deg (snd i) <= l =>
                          deg (snd i) < deg (fst i) => (snd i) <> poly0 =>
                          iter k gcdp_rec_it i = iter l gcdp_rec_it i.
- apply: natind => /= {p q} [|k k_ge0 kh]; 1: by smt(deg_eq0 ge0_deg).
  by apply: natind; smt(deg_eq0 ge0_deg iterSr iter_id ltn_modpN0).
case: (p = poly0) => [->|pnz]; 1: by rewrite modp0 mod0p gcdp0 gcd0p.
case: (q = poly0) => [->|qnz]; 1: by rewrite modp0 mod0p gcdp0 gcd0p.
rewrite /gcdp !ltn_modp pnz qnz /= pnz qnz /=.
case: (deg p < deg q) => /= [ltpq|leqp].
- rewrite qnz /=; case: (modp q p = poly0) => modP.
  + rewrite modP /= iter_id /=; 1: by smt().
    have [d [d_ge0 ->]] : exists d, 0 <= d /\ deg p = d + 1 by smt(deg_gt0).
    by rewrite iterSr // {2}/gcdp_rec_it /= modp0 pnz /= iter_id; smt(mod0p).
  + have [d [d_ge0 ->]] : exists d, 0 <= d /\ deg q = deg p + d + 1 by smt().
    rewrite iterSr; 1: by smt(ge0_deg).
    by rewrite {2}/gcdp_rec_it /= modP; smt(ltn_modpN0).
- rewrite pnz /=; case: (modp p q = poly0) => modP.
  + rewrite modP /= iter_id /=; 1: by smt().
    have [d [d_ge0 ->]] : exists d, 0 <= d /\ deg q = d + 1 by smt(deg_gt0).
    by rewrite iterSr // {2}/gcdp_rec_it /= modp0 qnz /= iter_id; smt(mod0p).
  + have [d [d_ge0 dE]] : exists d, 0 <= d /\ deg p = d + 1 by smt(deg_gt0).
    rewrite dE iterSr; 1: by smt(ge0_deg).
    by rewrite {2}/gcdp_rec_it /= modP; smt(ltn_modpN0).
qed.

lemma size_gcd1p p : deg (gcdp poly1 p) = 1
  by smt(deg1 deg_eq1 deg_gt0 gcdpE gcdp0 gcd0p modpC modp0 modp1).

lemma size_gcdp1 p : deg (gcdp p poly1) = 1
  by smt(deg1 deg_eq1 deg_gt0 gcdpE gcdp0 gcd0p modpC modp0 modp1).

lemma gcdpp : idempotent gcdp by move=> p; rewrite gcdpE /= modpp gcd0p.

lemma dvdp_gcdlr p q : dvdp (gcdp p q) p && dvdp (gcdp p q) q.
proof.
have [r ]: exists r, min (deg p) (deg q) < r by smt().
move: r p q; apply: natind; 1: by smt(deg_eq0 dvdpp gcdp0 ge0_deg).
by smt(dvdpp dvdp0 dvdp_mod gcdpE gcd0p ltn_modp).
qed.

lemma dvdp_gcdl p q : dvdp (gcdp p q) p by smt(dvdp_gcdlr).

lemma dvdp_gcdr p q : dvdp (gcdp p q) q by smt(dvdp_gcdlr).

lemma leq_gcdpl p q : p <> poly0 => deg (gcdp p q) <= deg p
  by smt(dvdp_gcdl dvdp_leq).

lemma leq_gcdpr p q : q <> poly0 => deg (gcdp p q) <= deg q
  by smt(dvdp_gcdr dvdp_leq).

lemma dvdp_gcd p m n : dvdp p (gcdp m n) = (dvdp p m && dvdp p n).
proof.
rewrite eqboolP iffE; split => [|[]]; 1: by smt(dvdp_trans dvdp_gcdl dvdp_gcdr).
have [r ] : exists r, min (deg m) (deg n) < r by smt().
move: r m n; apply: natind; 1: by smt(deg_eq0 dvdp0 gcdp0 ge0_deg).
by smt(dvdp_mod gcdpE gcdp0 gcd0p ltn_modp).
qed.

lemma gcdpC p q : eqp (gcdp p q) (gcdp q p)
  by smt(dvdp_gcd dvdp_gcdl dvdp_gcdr).

lemma gcd1p p : eqp (gcdp poly1 p) poly1.
proof.
rewrite -size_poly_eq1 gcdpE deg1.
by smt(degC deg1 deg_eq0 deg_eq1 gcdp0 gcd0p ge0_deg modpC modp0 modp1).
qed.

lemma gcdp1 p : eqp (gcdp p poly1) poly1 by smt(eqp_ltrans gcdpC gcd1p).

lemma gcdp_addl_mul (p q r : poly) : eqp (gcdp r (p * r + q)) (gcdp r q)
  by smt(PS.addKr dvdp_addr dvdp_gcd dvdp_gcdl dvdp_gcdr dvdp_mulr PS.mulNr).

lemma gcdp_addl (m n : poly) : eqp (gcdp m (m + n)) (gcdp m n)
  by rewrite -{2}PS.mul1r gcdp_addl_mul.

lemma gcdp_addr (m n : poly) : eqp (gcdp m (n + m)) (gcdp m n)
  by rewrite PS.addrC gcdp_addl.

lemma gcdp_mull (m n : poly) : eqp (gcdp n (m * n)) n.
proof.
case: (n = poly0) => [->|n_neq0]; 1: by rewrite gcd0p PS.mulr0 eqpxx.
case: (m = poly0) => [->|m_neq0]; 1: by rewrite PS.mul0r gcdp0 eqpxx.
rewrite gcdpE modp_mull gcd0p degM_proper; 1: by smt(lc_eq0 mulf_eq0).
by smt(deg_eq0 deg_eq1 dvdpZl eqpxx eqp_scale gcd0p ge0_deg modp_eq0 scalepE).
qed.

lemma gcdp_mulr (m n : poly) : eqp (gcdp n (n * m)) n
  by rewrite PS.mulrC gcdp_mull.

lemma gcdp_scalel c m n : c <> zeror => eqp (gcdp (c ** m) n) (gcdp m n)
  by smt(dvdp_gcd dvdp_gcdl dvdp_gcdr dvdp_trans dvdpZl dvdpZr).

lemma gcdp_scaler c m n : c <> zeror => eqp (gcdp m (c ** n)) (gcdp m n)
  by smt(eqp_trans gcdpC gcdp_scalel).

lemma dvdp_gcd_idl m n : dvdp m n => eqp (gcdp m n) m.
proof.
case: (m = poly0); 1: by smt(dvd0p eqpxx gcd0p).
by smt(dvdp_eq eqp_sym eqp_trans expf_eq0 gcdp_mull gcdp_scaler lc_eq0).
qed.

lemma dvdp_gcd_idr m n : dvdp n m => eqp (gcdp m n) n
  by smt(dvdp_gcd_idl eqp_trans gcdpC).

lemma gcdp_exp p k l :
  eqp (gcdp (PS.exp p k) (PS.exp p l)) (PS.exp p (min `|k| `|l|)).
proof.
suff: forall k l, 0 <= k /\ 0 <= l =>
                  eqp (gcdp (PS.exp p k) (PS.exp p l)) (PS.exp p (min k l)).
- case: (unitp p) => [up _|nup]; 2: by wlog: k l / 0 <= k /\ 0 <= l;
                                       smt(PS.exprV PS.unitout).
  suff: (eqp (gcdp (PS.exp p k) (PS.exp p l)) poly1)
    by smt(deg_eq1 eqp_trans polyC_eqp1 PS.unitrX).
  suff: exists c, c <> zeror /\ PS.exp p k = c ** poly1
    by smt(eqp_trans gcdp_scalel gcd1p).
  by smt(deg_eq1 mulr1 polyCM scalepE PS.unitrX).
move => {k l} k l [k_ge0 l_ge0]; case: (k <= l) => klP.
- rewrite lez_minl //; have -> : l = l - k + k by smt().
  by rewrite PS.exprD_nneg ?gcdp_mull /#.
- rewrite lez_minr => [/#|]; have -> : k = k - l + l by smt().
  by rewrite PS.exprD_nneg; smt(eqp_trans gcdpC gcdp_mull).
qed.

lemma gcdp_eq0 p q : (gcdp p q = poly0) = (p = poly0 && q = poly0)
  by smt(dvd0p dvdp_gcdl dvdp_gcdr).

lemma eqp_gcdr p q r : eqp q r => eqp (gcdp p q) (gcdp p r)
  by smt(dvdp_gcd dvdp_gcdl dvdp_gcdr eqp_dvdr).

lemma eqp_gcdl r p q : eqp p q => eqp (gcdp p r) (gcdp q r)
  by smt(dvdp_gcd dvdp_gcdl dvdp_gcdr eqp_dvdr).

lemma eqp_gcd p1 p2 q1 q2 :
  eqp p1 p2 => eqp q1 q2 => eqp (gcdp p1 q1) (gcdp p2 q2)
  by move => e1 e2; apply: (eqp_trans (gcdp p1 q2)); smt(eqp_gcdl eqp_gcdr).

lemma eqp_rgcd_gcd p q : eqp (rgcdp p q) (gcdp p q).
proof.
have [n ] : exists n, min (deg p) (deg q) <= n by smt().
move: n p q; apply natind; 1: by smt(deg_eq0 eqpxx ge0_deg gcdp0 rgcdp0).
move => /= n n_ge0 nh p q degP.
case: (p = poly0) => [->|p_neq0]; 1: by rewrite gcd0p rgcd0p eqpxx.
case: (q = poly0) => [->|q_neq0]; 1: by rewrite gcdp0 rgcdp0 eqpxx.
by rewrite gcdpE rgcdpE; smt(eqp_gcdl eqp_rmod_mod eqp_size eqp_trans ltn_modp).
qed.

lemma gcdp_modl m n : eqp (gcdp (modp m n) n) (gcdp m n)
  by smt(eqpxx eqp_sym gcdpE modp_small).

lemma gcdp_modr m n : eqp (gcdp m (modp n m)) (gcdp m n)
  by smt(eqp_trans gcdpC gcdp_modl).

lemma gcdp_def d m n :
  dvdp d m => dvdp d n => (forall d', dvdp d' m => dvdp d' n => dvdp d' d) =>
  eqp (gcdp m n) d by smt(dvdp_gcd dvdp_gcd dvdp_gcdr eqpxx).

op coprimep p q = deg (gcdp p q) = 1.

lemma coprimep_size_gcd p q : coprimep p q => deg (gcdp p q) = 1 by smt().

lemma coprimep_def p q : coprimep p q = (deg (gcdp p q) = 1) by smt().

lemma coprimepZl c m n :
  c <> zeror => coprimep (c ** m) n = coprimep m n by smt(eqp_size gcdp_scalel).

lemma coprimepZr c m n:
  c <> zeror => coprimep m (c ** n) = coprimep m n by smt(eqp_size gcdp_scaler).

lemma coprimepp p : coprimep p p = (deg p = 1) by smt(gcdpp).

lemma gcdp_eqp1 p q : eqp (gcdp p q) poly1 = coprimep p q by smt(size_poly_eq1).

lemma coprimep_sym p q : coprimep p q = coprimep q p
  by smt(eqp_ltrans gcdpC gcdp_eqp1).

lemma coprime1p p : coprimep poly1 p by smt(deg1 eqp_size gcd1p).

lemma coprimep1 p : coprimep p poly1 by smt(coprime1p coprimep_sym).

lemma coprimep0 p : coprimep p poly0 = eqp p poly1 by smt(gcdp0 size_poly_eq1).

lemma coprime0p p : coprimep poly0 p = eqp p poly1
  by smt(coprimep0 coprimep_sym).

lemma coprimepP p q :
  (forall d, dvdp d p => dvdp d q => eqp d poly1) = coprimep p q
  by smt(dvdp_eqp1 dvdp_gcd dvdp_gcdlr size_poly_eq1).

lemma coprimepPn p q :
  p <> poly0 =>
  (exists d, (dvdp d (gcdp p q)) /\ ! eqp d poly1) = ! coprimep p q
  by smt(dvdpp dvdp1 eqp_dvdr gcdp_eqp1 size_poly_eq1).

lemma coprimep_dvdl q p r : dvdp r q => coprimep p q => coprimep p r
  by smt(coprimepP dvdp_trans).

lemma coprimep_dvdr p q r : dvdp r p => coprimep p q => coprimep r q
  by smt(coprimep_dvdl coprimep_sym).

lemma coprimep_modl p q : coprimep (modp p q) q = coprimep p q
  by smt(gcdpE modp_small).

lemma coprimep_modr q p : coprimep q (modp p q) = coprimep q p
  by smt(coprimep_modl coprimep_sym).

lemma rcoprimep_coprimep q p : rcoprimep q p = coprimep q p
  by smt(eqp_rgcd_gcd eqp_size).

lemma eqp_coprimepr p q r : eqp q r => coprimep p q = coprimep p r
  by smt(gcdp_eqp1 eqp_gcdr eqp_ltrans).

lemma eqp_coprimepl p q r : eqp q r => coprimep q p = coprimep r p
  by smt(eqp_coprimepr coprimep_sym).

(* It will go through useless loops once "rp = poly0" since iter is needed
   as recursive calls are currently not allowed. *)
op egcdp_rec_it (i : poly * poly * poly * poly * poly * poly) =
  let (r, rp, u, v, up, vp) = i in
  if rp = poly0 then i else
    let rpp = modp r rp in
    let upp = exp (lc rp) (scalp r rp) ** u - up * divp r rp in
    let vpp = exp (lc rp) (scalp r rp) ** v - vp * divp r rp in
    (rp, rpp, up, vp, upp, vpp).

op egcdp_rec p q k =
  let i = (p, q, poly1, poly0, poly0, poly1) in
  let (r, rp, u, v, up, vp) = iter k egcdp_rec_it i in (u, v).

op egcdp p q =
  if deg q <= deg p then egcdp_rec p q (deg q)
  else let (u, v) = egcdp_rec q p (deg p) in (v, u).

lemma egcdp0 p : egcdp p poly0 = (poly1, poly0) by smt(deg0 ge0_deg iter0).

lemma egcdp_recP k p q :
  q <> poly0 => deg q <= k => deg q <= deg p =>
  let (u, v) = (egcdp_rec p q k) in
  deg u <= deg q /\ deg v <= deg p /\ eqp (gcdp p q) (u * p + v * q).
proof.
suff: forall k r rp u v up vp, let s = exp (lc rp) (scalp r rp) in
        rp <> poly0 => deg rp <= k => deg rp < deg r =>
        deg up <= deg q - deg r + 1 => deg vp <= deg p - deg r + 1 =>
        deg (s ** u - up * divp r rp) <= deg q - deg rp + 1 =>
        deg (s ** v - vp * divp r rp) <= deg p - deg rp + 1 =>
        r = u * p + v * q => rp = up * p + vp * q =>
        eqp (gcdp p q) (gcdp r rp) =>
        let i = iter k egcdp_rec_it (r, rp, u, v, up, vp) in
        let (r', rp', u', v', up', vp') = i in
        deg u' <= deg q /\ deg v' <= deg p /\
        eqp (gcdp r rp) (u' * p + v' * q).
- move: k p q; apply: natind; 1: by smt(deg_eq0 ge0_deg).
  move => /= k k_ge0 _ p q P q_neq0; rewrite /egcdp_rec /= iterSr //.
  rewrite {2}/egcdp_rec_it /= q_neq0 /= PS.mul0r PS.subr0 scalep0 scalepE.
  rewrite PS.mulr1 PS.add0r PS.mul1r; case: (modp p q = poly0) => [|mP kqP pqP].
  + move => mP; rewrite iter_id /egcdp_rec_it ?mP //= deg0 deg1 ge0_deg /=.
    by rewrite PS.mul0r PS.add0r PS.mul1r; smt(deg_ge1 dvdp_gcd_idr).
  + pose up := polyC (exp (lc q) (scalp p q)); pose vp := - divp p q.
    pose s := exp (lc (modp p q)) (scalp q (modp p q)).
    pose d := divp q (modp p q); have vpP : deg vp <= deg p - deg q + 1
      by smt(degN ler_maxr ltn_modp size_divp).
    have uppP : deg (s ** poly0 - up * d) <= deg q - deg (modp p q) + 1
      by rewrite scalep0 PS.add0r degN; smt(degZ_le ltn_modp scalepE size_divp).
    have vppP : deg (s ** poly1 - vp * d) <= deg p - deg (modp p q) + 1
      by smt(degB degC  degM divpN0 ltn_modp PS.mul0r polyCM scalepE size_divp).
    move: (P k q (modp p q) poly0 poly1 up vp).
    suff: q = poly0 * p + poly1 * q /\
          modp p q = polyC (exp (lc q) (scalp p q)) * p + (- divp p q) * q /\
          eqp (gcdp p q) (gcdp q (modp p q))
      by smt(deg0 deg1 degC eqp_trans ltn_modp).
    suff: modp p q = polyC (exp (lc q) (scalp p q)) * p + (- divp p q) * q
      by rewrite PS.mul0r PS.add0r PS.mul1r;
         smt(eqp_sym eqp_trans gcdpC gcdp_modr).
    by rewrite -scalepE divp_eq PS.mulNr PS.addrAC PS.subrr PS.add0r.
- move => {k}; apply: natind; 1: by smt(deg_eq0 ge0_deg).
  move => /= k k_ge0 kh r rp u v up vp rp_neq0 krpP rrpP uP vP upP vpP.
  move => rP rpP gcdpP; rewrite iterSr // {2}/egcdp_rec_it /= rp_neq0 /=.
  case: (modp r rp = poly0) => [|rpp_neq0];
    1: by smt(deg0 dvdp_gcd_idr eqp_trans iter_id ltn_modp subr0).
  pose s := exp (lc rp) (scalp r rp); pose d := divp r rp.
  have mP : modp r rp = (s ** u - up * d) * p + (s ** v - vp * d) * q.
  + rewrite /s /d !PS.mulrBl PS.addrACA -!scalerAl -scalepDr -rP.
    rewrite !(PS.mulrAC _ (divp r rp)) -PS.opprD -PS.mulrDl -rpP.
    by rewrite divp_eq PS.mulrC PS.addrAC PS.subrr PS.add0r.
  pose rq := modp r rp; pose t := exp (lc rq) (scalp rp rq).
  suff: deg (t ** up - (s ** u - up * d) * divp rp rq) <= deg q - deg rq + 1 /\
        deg (t ** vp - (s ** v - vp * d) * divp rp rq) <= deg p - deg rq + 1
    by smt(gcdpC gcdpE ltn_modp).
  suff: deg ((s ** u - up * d) * divp rp rq) <= deg q - deg rq + 1 /\
        deg ((s ** v - vp * d) * divp rp rq) <= deg p - deg rq + 1
    by smt(degB degZ_le ltn_modp).
  by smt(degM divpN0 ltn_modp PS.mul0r size_divp).
qed.

lemma egcdpP p q :
  p <> poly0 => q <> poly0 => forall u v, (u, v) = egcdp p q =>
  deg u <= deg q && deg v <= deg p && eqp (gcdp p q) (u * p + v * q)
  by smt(PS.addrC egcdp_recP eqp_trans gcdpC).

lemma egcdpE p q :
  forall u v, (u, v) = egcdp p q => eqp (gcdp p q) (u * p + v * q).
proof.
move => u v uvP; case: (q = poly0) => [|q_neq0];
  1: smt(PS.addr0 egcdp0 eqpxx gcdp0 PS.mulr0 PS.mul1r).
case: (p = poly0) =>[pE0|]; 2: by smt(egcdpP).
move: uvP; rewrite pE0 gcd0p PS.mulr0 PS.add0r /egcdp deg0.
smt(deg_eq0 eqpxx ge0_deg iter0 PS.mul1r).
qed.

lemma Bezoutp (p q : poly) : exists u v, eqp (u * p + v * q) (gcdp p q).
proof.
case: (p = poly0) => [|pnz]; 1: by smt(PS.add0r eqpxx gcd0p PS.mul0r PS.mul1r).
case: (q = poly0) => [|qnz]; 1: by smt(PS.addr0 eqpxx gcdp0 PS.mul0r PS.mul1r).
by pose e := (egcdp p q); exists (fst e) (snd e); smt(egcdpP eqp_sym).
qed.

lemma Bezout_coprimepP p q :
   (exists (u v : poly), eqp (u * p + v * q) poly1) = coprimep p q.
proof.
rewrite -gcdp_eqp1 eqboolP iffE; split; 2: by smt(Bezoutp eqp_trans).
by smt(eqp_dvdr dvdp_addr dvdp_gcdl dvdp_gcdr dvdp_mulr dvd1p eqp_sym).
qed.

lemma coprimep_root p q x :
  coprimep p q => root p x => peval q x <> zeror.
proof.
rewrite -Bezout_coprimepP; move => [u v uvP] rpx.
move: uvP; rewrite -eqpP; move => [c1 c2] [c1_neq0 [c2_neq0 cP]].
have: peval (c1 ** (u * p + v * q)) x <> zeror
  by smt(pevalC pevalD pevalM pevalZ mulr1).
by rewrite pevalZ pevalD !pevalM rpx mulr0 add0r; smt(mulf_eq0).
qed.

lemma Gauss_dvdpl p q d : coprimep d q => dvdp d (p * q) = dvdp d p.
proof.
rewrite -Bezout_coprimepP; move => [u v uvP].
rewrite eqboolP iffE; split; 2: smt(dvdp_mull).
move: (eqp_mull _ p _ uvP); rewrite PS.mulr1 PS.mulrDr eqp_sym => {uvP} peq dpq.
rewrite (eqp_dvdr _ _ _ peq) dvdp_addr; 1: by smt(dvdpp dvdp_mulr PS.mulrA).
by rewrite PS.mulrA PS.mulrAC dvdp_mull.
qed.

lemma Gauss_dvdpr p q d : coprimep d q => dvdp d (q * p) = dvdp d p
  by smt(Gauss_dvdpl PS.mulrC).

lemma Gauss_dvdp m n p :
  coprimep m n => dvdp (m * n) p = (dvdp m p && dvdp n p).
proof.
case: (m = poly0) => [|m_neq0]; 1: by smt(coprime0p dvdUp dvd0p PS.mul0r).
case: (n = poly0) => [|n_neq0]; 1: by smt(coprimep0 dvdUp dvd0p PS.mulr0).
move => hc; rewrite eqboolP iffE; split => [mnmp|[dmp dnp]].
- have: dvdp (m * n) (m * p) /\ dvdp (m * n) (p * n)
    by smt(dvdp_mull dvdp_mulr).
  by smt(dvdp_mul2l dvdp_mul2r).
- have: dvdp m (divp p n) = dvdp m (divp p n * n) by smt(Gauss_dvdpl).
  move: (dnp); rewrite dvdp_eq => e2; rewrite -e2 dvdpZr ?lc_expn_scalp_neq0 //.
  rewrite dmp eqT dvdp_eq => e3.
  apply: (eq_dvdp (exp (lc m) (scalp (divp p n) m) * exp (lc n) (scalp p n))
                  (divp (divp p n) m)); 1: by smt(lc_expn_scalp_neq0 mulf_eq0).
  by rewrite PS.mulrA -e3 -scalerAl -e2 scalepA.
qed.

lemma Gauss_gcdpr p m n : coprimep p m => eqp (gcdp p (m * n)) (gcdp p n).
proof.
rewrite /eqp  !dvdp_gcd !dvdp_gcdl /= dvdp_mulr ?dvdp_gcdr //=.
by smt(coprimepP dvdp_gcd dvdp_gcdr Gauss_dvdpl PS.mulrC).
qed.

lemma Gauss_gcdpl p m n : coprimep p n => eqp (gcdp p (m * n)) (gcdp p m)
  by smt(Gauss_gcdpr PS.mulrC).

lemma coprimepMr (p q r : poly) :
  coprimep p (q * r) = (coprimep p q && coprimep p r)
  by smt(coprimepP coprimep_dvdr dvdp_mull dvdp_mulr Gauss_dvdpl).

lemma coprimepMl (p q r : poly) :
  coprimep (q * r) p = (coprimep q p && coprimep r p)
  by smt(coprimepMr coprimep_sym).

lemma modp_coprime k u n :
  k <> poly0 => eqp (modp (k * u) n) poly1 => coprimep k n.
proof.
move=> k_neq0 hmod; rewrite -Bezout_coprimepP.
exists (exp (lc n) (scalp (k * u) n) ** u) (- divp ( k * u) n).
rewrite -scalerAl PS.mulrC (divp_eq (u * k) n) PS.mulNr -PS.addrAC PS.subrr.
by rewrite PS.add0r PS.mulrC.
qed.

lemma coprimep_pexpl k m n :
  0 < k => coprimep (PS.exp m k) n = coprimep m n
  by move: k; apply: natind; smt(coprimepMl PS.expr1 PS.exprS).

lemma coprimep_pexpr k m n :
  0 < k => coprimep m (PS.exp n k) = coprimep m n
  by smt(coprimep_pexpl coprimep_sym).

lemma coprimep_expl k m n : coprimep m n => coprimep (PS.exp m k) n.
proof.
have kgzP : forall k m n, 0 <= k => coprimep m n => coprimep (PS.exp m k) n
  by apply: natind; smt(coprime1p coprimep_pexpl PS.expr0).
case: (unitp m) => [up|nup]; 2: by wlog: k / 0 <= k; smt(PS.exprV PS.unitout).
have [c [c_neq0 ->]] : exists c, c <> zeror /\ PS.exp m k = c ** poly1
  by smt(deg_eq1 mulr1 polyCM scalepE PS.unitrX).
by rewrite coprimepZl // coprime1p.
qed.

lemma coprimep_expr k m n : coprimep m n => coprimep m (PS.exp n k)
  by smt(coprimep_expl coprimep_sym).

lemma gcdp_mul2l (p q r : poly) : eqp (gcdp (p * q) (p * r)) (p * gcdp q r).
proof.
case: (p = poly0) => [|p_neq0]; 1: by smt(eqpxx gcdp0 PS.mul0r).
rewrite /eqp !dvdp_gcd !dvdp_mul2l // dvdp_gcdr dvdp_gcdl /=.
move: (Bezoutp q r) => [u v] huv; rewrite eqp_sym in huv.
rewrite (eqp_dvdr _ _ _ (eqp_mull _ _ _ huv)).
rewrite PS.mulrDr (PS.mulrCA p u) (PS.mulrCA p v).
by smt(dvdp_add dvdp_mulr dvdp_gcdr dvdp_gcdl).
qed.

lemma gcdp_mul2r (q r p : poly) : eqp (gcdp (q * p) (r * p)) (gcdp q r * p)
  by smt(gcdp_mul2l PS.mulrC).

lemma mulp_gcdr p q r : eqp (r * (gcdp p q)) (gcdp (r * p) (r * q))
  by rewrite eqp_sym gcdp_mul2l.

lemma mulp_gcdl p q r : eqp ((gcdp p q) * r) (gcdp (p * r) (q * r))
  by rewrite eqp_sym gcdp_mul2r.

lemma coprimep_div_gcd p q :
  (p <> poly0) || (q <> poly0) =>
  coprimep (divp p (gcdp p q)) (divp q (gcdp p q)).
proof.
rewrite oraE -negb_and -andaE -gcdp_eq0 -gcdp_eqp1 => gpq0.
rewrite -(eqp_mul2r (gcdp p q)) // PS.mul1r.
by smt(dvdp_eq dvdp_gcdl dvdp_gcdr eqp_gcd eqp_ltrans
       eqp_scale expf_eq0 lc_eq0 mulp_gcdl).
qed.

lemma divp_eq0 p q :
  (divp p q = poly0) = (p = poly0 || q = poly0 || deg p < deg q).
proof.
rewrite eqboolP iffE; split; 2: by smt(divp0 div0p divp_small).
by smt(PS.add0r degZ_lreg divp_eq lc_expn_scalp_neq0 lregP ltn_modp PS.mul0r).
qed.

lemma dvdp_div_eq0 p q : dvdp q p => (divp p q = poly0) = (p = poly0)
  by smt(divp_eq0 div0p dvdp_leq dvd0p eqpxx).

lemma Bezout_coprimepPn p q :
  p <> poly0 => q <> poly0 =>
  (exists u v, 0 < deg u < deg q /\ 0 < deg v < deg p /\ u * p = v * q) =
  ! coprimep p q.
proof.
move => p_neq0 q_neq0; rewrite eqboolP iffE; split.
- move => [u v] [[ps1 s1] [[ps2 s2] e]].
  have: ! deg (q * p) <= deg (u * p)
    by smt(degM_proper deg_eq0 mulf_eq0 lc_eq0).
  apply: contra => hc; apply: dvdp_leq; 1: by smt(deg_gt0 PS.mulf_eq0).
  by rewrite PS.mulrC Gauss_dvdp // dvdp_mulr ?dvdpp /= e dvdp_mulr dvdpp.
- move => hc; have {hc} : 1 < deg (gcdp p q) by smt(deg_eq0 gcdp_eq0 ge0_deg).
  have [n nP] : exists n, deg (gcdp p q) = n by smt().
  move: n p q p_neq0 q_neq0 nP; apply natind => [/#|/=]; apply: natind => [/#|].
  move => /= n n_ge0 _ _ _ p q p_neq0 q_neq0 degE degP.
  move: (dvdp_gcdl p q) (dvdp_gcdr p q); rewrite !dvdp_eq => hu1 hv1.
  exists (exp (lc (gcdp p q)) (scalp p (gcdp p q)) ** divp q (gcdp p q)).
  exists (exp (lc (gcdp p q)) (scalp q (gcdp p q)) ** divp p (gcdp p q)).
  rewrite -!scalerAl !scalerAr hu1 hv1 PS.mulrCA /=.
  rewrite !degZ_lreg ?lregP ?lc_expn_scalp_neq0 // !deg_gt0 !divp_eq0 gcdp_eq0.
  rewrite p_neq0 q_neq0 /= -!lerNgt leq_gcdpl //  leq_gcdpr //=.
  rewrite !ltn_divpl ?gcdp_eq0 ?p_neq0 ?q_neq0 //.
  by rewrite !degM_proper; smt(gcdp_eq0 lc_eq0 mulf_eq0).
qed.

lemma dvdp_pexp2r m n k :
  0 < k => dvdp (PS.exp m k) (PS.exp n k) = dvdp m n.
proof.
move => k_gt0; rewrite eqboolP iffE; split; 2: by exact: dvdp_exp2r.
case: (n = poly0) => [|n_neq0]; 1: by smt(dvdp0).
case: (m = poly0) => [|m_neq0]; 1: by smt(dvd0pP PS.expf_eq0 PS.expr0n).
move: (dvdp_gcdl m n)(dvdp_gcdr m n); rewrite 2!dvdp_eq => def_m def_n.
have gcdp_neq0 : gcdp m n <> poly0 by smt(gcdp_eq0).
rewrite -(dvdpZr (exp (exp (lc (gcdp m n)) (scalp n (gcdp m n))) k));
  1: by smt(expf_eq0 lc_eq0).
rewrite -(dvdpZl (exp (exp (lc (gcdp m n)) (scalp m (gcdp m n))) k));
  1: by smt(expf_eq0 lc_eq0).
rewrite !scalepE -!(polyCX _ k) -?PS.exprMn -?scalepE; 1..4: by smt().
rewrite def_m def_n !PS.exprMn; 1, 2: by smt().
rewrite dvdp_mul2r ?PS.expf_eq0 ?gcdp_neq0 //.
have: coprimep (PS.exp (divp m (gcdp m n)) k) (PS.exp (divp n (gcdp m n)) k)
  by smt(coprimep_div_gcd coprimep_pexpl coprimep_pexpr).
rewrite -coprimepP => hc hd; suff: deg (divp m (gcdp m n)) = 1.
- rewrite -(dvdpZl (exp (lc (gcdp m n)) (scalp m (gcdp m n))));
    1: by smt(expf_eq0 lc_eq0).
  rewrite -(dvdpZr (exp (lc (gcdp m n)) (scalp n (gcdp m n))));
    1: by smt(expf_eq0 lc_eq0).
  rewrite deg_eq1; move => [c [c_neq0 cP]]; rewrite def_m def_n cP -scalepE.
  by rewrite dvdpZl // dvdp_mulr ?dvdpp.
- case: (divp m (gcdp m n) = poly0) => [|m'_neq0];
    1: by smt(eq_polyC0 expf_eq0 lc_eq0 PS.mulf_eq0 PS.mul0r scalepE).
  move: (hc (PS.exp (divp m (gcdp m n)) k)); rewrite dvdpp hd /= -size_poly_eq1.
  by rewrite degXn_proper ?lregP ?lc_eq0; smt(expf_eq0).
qed.

lemma root_gcd p q x : root (gcdp p q) x = (root p x && root q x).
proof.
rewrite /= !root_factor_theorem eqboolP iffE.
split; 1: by smt(dvdp_trans dvdp_gcdl dvdp_gcdr).
by smt(Bezoutp dvdp_addl dvdp_mulr eqp_dvdr eqp_sym).
qed.

lemma root_biggcd x ps :
  root (foldr gcdp poly0 ps) x = all (fun p => root p x) ps
  by elim ps; smt(root0 root_gcd).

(* It will go through useless loops once "coprimep p q"
   since iter is needed as recursive calls are currently not allowed. *)
op gdcop_rec_it (i : poly * poly) =
  let (q, p) = i in
  if coprimep p q then i else (q, divp p (gcdp p q)).

op gdcop_rec (q p : poly) (k : int) =
  if k <= 0 then eqpoly0p q else let (pp, qq) = iter k gdcop_rec_it (q, p) in qq.

op gdcop (q p : poly) = gdcop_rec q p (deg p).

op gdcop_spec (q p r : poly) =
  dvdp r p && (coprimep r q || p = poly0) &&
  (forall d, dvdp d p => coprimep d q => dvdp d r).

lemma gdcop0 q : gdcop q poly0 = eqpoly0p q by smt(deg0).

lemma gdcop_recP q p k : deg p <= k => gdcop_spec q p (gdcop_rec q p k).
proof.
rewrite /gdcop_spec; move: k p q; apply: natind;
  1: by smt(coprimep0 deg0 deg_eq0 dvdp0 dvdUp ge0_deg).
move => /= k k_ge0 kP p q kpP; case: (coprimep p q); 1: by smt(dvdpp iter_id).
case: (p = poly0) => [|/= p_neq0]; 1: by smt(div0p dvdp0 iter_id).
case: (q = poly0) => [-> pqP|q_neq0 cop].
- rewrite /gdcop_rec; have -> /= : ! k + 1 <= 0 by smt().
  suff: iter (k + 1) gdcop_rec_it (poly0, p) =
        (poly0, polyC (exp (lc p) (scalp p p)))
    by smt(coprimep0 dvdUp lc_expn_scalp_neq0 polyC_eqp1).
  rewrite iterSr // iter_id; 2: by smt(divpp gcdp0).
  by smt(coprimep0 divpp gcdp0 iterSr iter_id lc_expn_scalp_neq0 polyC_eqp1).
- move: (dvdp_gcdl p q); rewrite dvdp_eq => e.
  have dgp : deg (gcdp p q) <= deg p by smt(dvdp_gcdl dvdp_leq gcdp_eq0).
  have p'_neq0 : divp p (gcdp p q) <> poly0
    by smt(dvdpN0 dvdp_mulIl eq_polyC0 PS.mulf_eq0 lc_expn_scalp_neq0 scalepE).
  have g_neq0 : gcdp p q <> poly0 by smt(gcdp_eq0).
  have dp' : deg (divp p (gcdp p q)) <= k by smt(deg_gt0 size_divp).
  suff: gdcop_spec q p (gdcop_rec q (divp p (gcdp p q)) k)
    by smt(deg_eq0 ge0_deg iterSr).
  move: (kP (divp p (gcdp p q)) q dp'); rewrite /gdcop_spec /gdcop_rec.
  have -> /= : ! k <= 0 by smt(deg_eq0 ge0_deg).
  rewrite p_neq0 p'_neq0 /=; move => [dr'p' [cr'q maxr']]; rewrite cr'q /=.
  split => [|_ d dp cdq]; 1: smt(divp_dvd dvdp_gcdl dvdp_trans).
  apply: maxr' => //.
  case: (dvdp d (gcdp p q)); 1: by smt(coprimepPn dvdpp dvdUp dvd0p dvdp_gcd).
  by smt(coprimep_dvdl dvdp_gcdr eqp_dvdr eqp_scale
         Gauss_dvdpl lc_expn_scalp_neq0).
qed.

lemma gdcopP q p : gdcop_spec q p (gdcop q p) by smt(gdcop_recP).

lemma coprimep_gdco p q : q <> poly0 => coprimep (gdcop p q) p by smt(gdcopP).

lemma size2_dvdp_gdco p q d :
  p <> poly0 => deg d = 2 =>
  dvdp d (gdcop q p) = (dvdp d p && ! (dvdp d q)).
proof.
case: (d = poly0) =>[|d_neq0 p_neq0 degdP]; 1: by smt(deg0).
rewrite eqboolP iffE; split.
- move: (gdcopP q p); rewrite /gdcop_spec; pose r := gdcop q p.
  rewrite p_neq0 /=; move => [rp [crq maxr]] dr; rewrite (dvdp_trans r) //=.
  suff /# : dvdp d q => ! coprimep r q.
  move => dq; rewrite -coprimepPn; 1: by smt(dvd0p).
  by exists d; rewrite dvdp_gcd dr dq /= -size_poly_eq1 degdP.
- move: (gdcopP q p); rewrite /gdcop_spec; pose r := gdcop q p.
  rewrite p_neq0 /=; move => [rp [crq maxr]] [dp dq]; apply: maxr => //.
  rewrite -coprimepP => x xd xq; move: (dvdp_leq x d d_neq0 xd).
  by rewrite -size_poly_eq1; smt(deg_eq0 dvd0p dvdp_size_eqp eqp_dvdl ge0_deg).
qed.

lemma dvdp_gdco p q : dvdp (gdcop p q) q by smt(gdcopP).

lemma root_gdco p q x :
  p <> poly0 => root (gdcop q p) x = (root p x && ! root q x).
proof.
move => p_neq0; rewrite !root_factor_theorem.
by apply: size2_dvdp_gdco; rewrite ?p0 // degNXC.
qed.

op comp_poly (p q : poly) =
  BigPoly.PCA.bigi predT (fun i => p.[i] ** PS.exp q i) 0 (deg p).

lemma comp_poly0 p : comp_poly poly0 p = poly0
  by rewrite /comp_poly deg0 range_geq // BigPoly.PCA.big_nil.

lemma comp_polyC c p : comp_poly (polyC c) p = polyC c.
proof.
case: (c = zeror) => [|c_neq0]; 1: by smt(comp_poly0).
rewrite /comp_poly degC c_neq0 /= BigPoly.PCA.big_int1 /=.
by rewrite polyCE /= PS.expr0 scalepE -polyCM mulr1.
qed.

lemma comp_polyD (p q r : poly) :
  comp_poly (p + q) r = comp_poly p r + comp_poly q r.
proof.
pose P := fun i => p.[i] ** PS.exp r i; pose Q := fun i => q.[i] ** PS.exp r i.
have <- : BigPoly.PCA.bigi predT (fun i => P i + Q i) 0 (deg (p + q)) =
          comp_poly (p + q) r by smt(polyDE scalepDl).
rewrite /comp_poly -BigPoly.PCA.sumrD.
have -> : BigPoly.PCA.bigi predT P 0 (deg p) =
          BigPoly.PCA.bigi predT P 0 (max (deg p) (deg q)).
- rewrite eq_sym (BigPoly.PCA.big_cat_int (deg p));
  by smt(PS.addr0 BigPoly.PCA.big1_seq gedeg_coeff ge0_deg mem_range scale0p).
have -> : BigPoly.PCA.bigi predT Q 0 (deg q) =
          BigPoly.PCA.bigi predT Q 0 (max (deg p) (deg q)).
- rewrite eq_sym (BigPoly.PCA.big_cat_int (deg q));
  by smt(PS.addr0 BigPoly.PCA.big1_seq gedeg_coeff ge0_deg mem_range scale0p).
rewrite !BigPoly.PCA.sumrD.
case: (deg (p + q) < max (deg p) (deg q)) => pqP; 2: by smt(degD mulrDl polyDE).
rewrite eq_sym (BigPoly.PCA.big_cat_int (deg (p + q))); 1, 2: by smt(ge0_deg).
rewrite -PS.subr_eq0 PS.addrAC PS.subrr PS.add0r.
rewrite BigPoly.PCA.big1_seq //= => i [_ ]; rewrite mem_range /P /Q.
by rewrite -scalepDl -polyDE; smt(gedeg_coeff scale0p).
qed.

lemma comp_polyZ c (p q : poly) : comp_poly (c ** p) q = c ** comp_poly p q.
proof.
case: (c = zeror) => [->|c_neq0]; 1: by rewrite !scale0p comp_poly0.
rewrite /comp_poly degZ_lreg ?lregP //.
by smt(PS.mulrA BigPoly.PCA.mulr_sumr polyCM polyZE scalepE).
qed.

lemma comp_polyM (p q r : poly) :
  comp_poly (p * q) r = comp_poly p r * comp_poly q r.
proof.
suff /# : forall n, deg p <= n =>
                    comp_poly (p * q) r = comp_poly p r * comp_poly q r.
move => n; move: n p q r; apply natind => [|/= n n_ge0 nh p q r npP];
  1: smt(comp_poly0 deg_eq0 ge0_deg PS.mul0r).
have pP : forall n p, deg p <= n + 1 =>
                      p = p - p.[n] ** polyXn n + p.[n] ** polyXn n
  by move => *; rewrite PS.addrAC -PS.addrA PS.subrr PS.addr0.
pose plt := p.[n] ** polyXn n; pose pr := p - plt.
rewrite (pP n p) // PS.mulrDl comp_polyD -/plt -/pr; have prP : deg pr <= n.
- have {pP} pltP : deg plt <= n + 1 by smt(degXn degZ_le).
  suff: pr.[n] = zeror by smt(degB deg_leP gedeg_coeff).
  by rewrite /pr /plt polyDE polyNE polyZE polyXnE n_ge0 /= mulr1 subrr.
suff: comp_poly (plt * q) r = comp_poly plt r * comp_poly q r
  by smt(comp_polyD PS.mulrDl).
rewrite /plt -scalerAl !comp_polyZ.
case: (p.[n] = zeror) => [|pnP]; 1: by smt(PS.mul0r scale0p).
rewrite -PS.subr_eq0 -scalerAl -scalepBr scalepE PS.mulf_eq0 eq_polyC0 pnP /=.
rewrite PS.subr_eq0 => {nh p npP plt pr prP pnP}; move: n n_ge0 q r.
suff /# : forall n m p q, 0 <= m => deg p <= n =>
                          comp_poly (polyXn m * p) q =
                          comp_poly (polyXn m) q * comp_poly p q.
apply natind; 1: by smt(comp_poly0 deg_eq0 ge0_deg PS.mulr0).
move => /= n n_ge0 nh m p q m_ge0 pnP; rewrite (pP n p) //; pose Xm := polyXn m.
pose plt := p.[n] ** polyXn n; pose pr := p - plt; rewrite PS.mulrDr comp_polyD.
have -> : comp_poly (Xm * plt) q = comp_poly Xm q * comp_poly plt q.
- rewrite /plt -scalerAr !comp_polyZ -scalerAr; pose Xn := polyXn n.
  suff /# : comp_poly (Xm * Xn) q = comp_poly Xm q * comp_poly Xn q.
  have mDn_ge0 : 0 <= m + n by smt().
  rewrite /comp_poly polyMXn2 m_ge0 n_ge0 /= !degXn //.
  rewrite !BigPoly.PCA.big_int_recr_cond //.
  rewrite !BigPoly.PCA.big1_seq; 1..3: by smt(mem_range polyXnE scale0p).
  rewrite !PS.add0r /predT /= !polyXnE m_ge0 n_ge0 mDn_ge0 /=.
  by rewrite !scalepE !PS.mul1r PS.exprD_nneg.
suff: deg pr <= n by smt(comp_polyD PS.mulrDr).
have {pP} pltP : deg plt <= n + 1 by smt(degXn degZ_le).
suff: pr.[n] = zeror by smt(degB deg_leP gedeg_coeff).
by rewrite /pr /plt polyDE polyNE polyZE polyXnE n_ge0 /= mulr1 subrr.
qed.

lemma dvdp_comp_poly r p q : dvdp p q => dvdp (comp_poly p r) (comp_poly q r).
proof.
case: (p = poly0) => [|p_neq0 pqP]; 1: by smt(comp_poly0 dvd0p).
apply: (eq_dvdp (exp (lc p) (scalp q p)) (comp_poly (divp q p) r));
by smt(comp_polyM comp_polyZ dvdp_eq expf_eq0 lc_eq0).
qed.

lemma gcdp_comp_poly r p q :
  eqp (comp_poly (gcdp p q) r) (gcdp (comp_poly p r) (comp_poly q r)).
proof.
split; 1: by rewrite dvdp_gcd !dvdp_comp_poly ?dvdp_gcdl ?dvdp_gcdr.
move: (Bezoutp p q) => [u v] [H _]; move: (dvdp_comp_poly r _ _ H) => {H} Huv _.
rewrite (dvdp_trans _ _ _ _ Huv) comp_polyD !comp_polyM.
by rewrite dvdp_add dvdp_mulr ?dvdp_gcdl dvdp_gcdr.
qed.

lemma coprimep_comp_poly r p q :
  coprimep p q => coprimep (comp_poly p r) (comp_poly q r).
proof.
rewrite -!gcdp_eqp1 -!size_poly_eq1 -!dvdp1 => H.
by move: (dvdp_comp_poly r _ _ H); smt(comp_polyC dvdp_trans gcdp_comp_poly).
qed.

lemma coprimep_addl_mul (p q r : poly) : coprimep r (p * r + q) = coprimep r q
  by smt(eqp_size gcdp_addl_mul).

(*-----------------------------------------------------------*)
(*TODO: put at the right place in PolyDiv.*)
lemma dvd_eqp_divr d p q :
  dvdp p d =>
  eqp p q =>
  eqp (divp d p) (divp d q).
proof.
case: (p = poly0) => [->>|neqp0]; [by rewrite dvd0p eqp_sym eqp0 => ->> ->>; apply/eqpxx|].
case: (q = poly0) => [->>|neqq0]; [by rewrite eqp0 neqp0|].
move=> dvdpd eq_; move: (dvdpd); rewrite (eqp_dvdl _ _ d eq_) => dvdqd.
move: eq_; rewrite -!eqpP => -[] c1 c2 [] neqc10 [] neqc20 eq_.
exists (( * ) c2 (exp (lc q) (scalp d q))) (( * ) c1 (exp (lc p) (scalp d p))).
rewrite !mulf_neq0 ?lc_expn_scalp_neq0 //=; apply/(IDPoly.mulfI (c1 ** p)).
+ by rewrite -scaler_eq0 negb_or neqc10.
rewrite {2}eq_ -!scalerAr -!scalerAl !scalepA (mulrC c2) !divpKC //.
rewrite !scalepA (mulrAC _ _ c1) (mulrC _ c1) !(mulrAC _ _ c2).
by rewrite (mulrAC _ (IDC.exp _ _)).
qed.

lemma dvdp_prod d p (ps : poly list) :
  p \in ps =>
  dvdp d p =>
  dvdp d (BigPoly.PCM.big predT idfun ps).
proof.
elim: ps => [|q ps IHps] //=; rewrite BigPoly.PCM.big_cons /(predT q) /(idfun q) /=.
by case=> [<<-|/IHps {IHps} IHps /IHps]; [apply/dvdp_mull|apply/dvdp_mulr].
qed.

lemma deg_eqp p :
  (deg p = 1) <=> eqp p poly1.
proof.
rewrite -eqpP; split=> [/deg_eq1 [c] [neqc0 ->>]|[c1 c2]].
+ by exists oner c; rewrite oner_neq0 neqc0 scale1r scalep1.
case=> neqc10 [] neqc20; rewrite scalep1 => eq_.
by move/(congr1 deg): eq_; rewrite degC degZ_lreg ?lregP // neqc20.
qed.

lemma unit_eqp p :
  (PolyComRing.unit p) => eqp p poly1.
proof. by move/unit_deg; apply/deg_eqp. qed.

lemma unit_eqp1 c :
  IDC.unit c => eqp (polyC c) poly1.
proof. by move=> uc; apply/unit_eqp/unitpP; exists c. qed.
(*TODO: end of put at the right place in PolyDiv.*)


(*-----------------------------------------------------------*)
(*TODO: change every relevant thing to use the monic operator and put at the right place in PolyDiv.*)
lemma monic_deg p :
  monic p =>
  0 < deg p.
proof. by rewrite deg_gt0 -lc_eq0 => ->; rewrite oner_neq0. qed.

lemma monic_exp_scalp p q :
  monic q =>
  IDC.exp (P.lc q) (scalp p q) = IDC.oner.
proof. by move=> ->; rewrite IDC.expr1z. qed.

lemma monic_divp_eq p q :
  monic q =>
  p = (+) (P.( * ) (divp p q) q) (modp p q).
proof.
by move=> uq; rewrite -divp_eq monic_exp_scalp // scalepE PolyComRing.mul1r.
qed.

lemma dvdp_monic_divp p q :
  dvdp q p =>
  monic p =>
  monic q =>
  monic (divp p q).
proof.
move=> dvd_ up uq; move: (up); rewrite {1}(monic_divp_eq p q) //.
rewrite dvd_ PolyComRing.addr0.
move: up uq; rewrite /monic => eqp eqq.
by rewrite lcM eqq IDC.mulr1.
qed.
(*TODO: end of change every relevant thing to use the monic operator and put at the right place in PolyDiv.*)


(*-----------------------------------------------------------*)
(*TODO: put at the right place in PolyDiv.*)
op scaled_monic p = exists c r , c <> zeror /\ monic r /\ p = c ** r.

lemma scaled_monic_eqp p :
  scaled_monic p <=>
  exists q , monic q /\ eqp p q.
proof.
split=> [[c r] [] neqc0 [] m_ ->>|[q] [] m_ eqp_].
+ by exists r; rewrite m_ /= eqp_scale.
exists (lc p) q; rewrite m_ lc_eq0; move/eqp_eq: (eqp_).
rewrite m_ scale1r => <- /=; apply/negP=> ->>; move: eqp_.
by rewrite eqp_sym eqp0 => ->>; move: m_; rewrite monicC eq_sym oner_neq0.
qed.

lemma scaled_monicC c : scaled_monic (polyC c) <=> c <> zeror.
proof.
split=> [[d r] [] neqd0 [] m_|neqc0]; [|by exists c poly1; rewrite neqc0 monic1 scalep1].
move/(congr1 deg); rewrite degZ_lreg ?lregP // degC; case (c = zeror) => //.
by move=> ->> /eq_sym /deg_eq0 ->>; move: m_; rewrite monicC eq_sym oner_neq0.
qed.

lemma scaled_monicM p q :
  scaled_monic (p * q)%P <=>
  (scaled_monic p /\ scaled_monic q).
proof.
split=> [[c r] [] neqc0 [] m_ eq_|[] [cp rp] [] neqcp0 [] m_p ->> [cq rq] [] neqcq0 [] m_q ->>]; last first.
+ rewrite -scalerAl -scalerAr scalepA; exists (cp * cq) (rp * rq).
  by rewrite mulf_eq0 negb_or neqcp0 neqcq0 /=; apply/monicM.
pose ip := argmax ("_.[_]" p) (fun x => forall y, x <> (lc p) * y).
pose iq := argmax ("_.[_]" q) (fun x => forall y, x <> (lc q) * y).
admit.
qed.

lemma scaled_monic_prod ['a] P F (s : 'a list) :
  scaled_monic (BigPoly.PCM.big P F s) <=>
  all (fun x => P x => scaled_monic (F x)) s.
proof.
elim: s => [|x s IHs]; [by rewrite BigPoly.PCM.big_nil scaled_monicC oner_neq0|].
by rewrite BigPoly.PCM.big_cons /=; case: (P x) => //= Px; rewrite scaled_monicM IHs.
qed.
(*TODO: end of put at the right place in PolyDiv.*)


(*-----------------------------------------------------------*)
op irreducible_poly p =
  (1 < deg p) && (forall q, deg q <> 1 => dvdp q p => eqp q p).

lemma irredp_poly_deg p :
  irreducible_poly p =>
  1 < deg p.
proof. by case. qed.

lemma Gauss_dvdpor (p q d : poly) :
  irreducible_poly d => dvdp d (p * q) = (dvdp d p || dvdp d q).
proof.
move => dP; case: (dvdp d p) => [|/= dpP]; 1: by smt(dvdp_mull).
rewrite eqboolP iffE; split => [dpqP|]; 2: by smt(dvdp_mulr).
suff: coprimep d p by smt(Gauss_dvdpr).
rewrite -coprimepP => r; case: (deg r = 1) => [|rP]; 1: by smt(size_poly_eq1).
move: dP => [ddP E] rdP rpP; move: (E r rP rdP); smt(dvdp_trans).
qed.

lemma irredp_poly_scale c p :
  c <> zeror =>
  irreducible_poly p <=>
  irreducible_poly (c ** p).
proof.
move=> neqc0; rewrite /irreducible_poly degZ_lreg ?lregP // !andaE.
apply/andb_id2l => _; apply/eq_iff/forall_eq => q /=.
rewrite dvdpZr //; apply/eq_iff/implyb_id2l => _.
apply/implyb_id2l => _; move: (eqp_scale p _ neqc0) => eqp_.
by rewrite !(eqp_sym q); split; apply/eqp_trans => //; rewrite eqp_sym.
qed.

lemma irredp_poly0 : ! irreducible_poly poly0 by rewrite /irreducible_poly deg0.

lemma irredp_neq0 p : irreducible_poly p => p <> poly0
  by apply/implybN => ->>; apply/irredp_poly0.

lemma irredp_polyC c : ! irreducible_poly (polyC c)
  by rewrite /irreducible_poly degC /=; case (_ = IDC.zeror).

lemma irreducible_poly_neqC q c :
  irreducible_poly q => q <> polyC c
  by apply/implybN => ->>; apply/irredp_polyC.

lemma irredp_eqp p q :
  eqp p q =>
  irreducible_poly p =>
  irreducible_poly q.
proof.
move=> eqp_; case=> deg_ forall_; split; [by move/eqp_size: eqp_ => <-|].
move=> _ r neq_ dvd_; move/(_ _ neq_ _): forall_; [by rewrite (eqp_dvdr _ _ _ eqp_)|].
by move=> eqp__; apply/(eqp_trans _ _ _ eqp__).
qed.

lemma irredp_deg2 p :
  deg p = 2 =>
  irreducible_poly p.
proof.
move=> degp; rewrite /irreducible_poly degp /= => q.
case/neq_ltz => [/ltzE/ler_subr_addr/P.deg_le0 ->>|].
+ by rewrite dvd0p => ->>; rewrite eqpxx.
move=> lt_ dvdp_; rewrite -dvdp_size_eqp //.
move: (dvdp_leq q p); rewrite -P.deg_eq0 degp dvdp_ /= => le_.
by apply/ler_anti; rewrite le_ /=; apply/ltzS/ltr_subl_addr.
qed.

lemma irredp_XsubC c : irreducible_poly (polyX - polyC c)
  by rewrite irredp_deg2 degNXC.

lemma poly1_or_dvdp_i p:
  deg p = 1 \/ exists q , irreducible_poly q /\ dvdp q p.
proof.
move: (P.ge0_deg p) (lerr (P.deg p)); move: {1 3}(P.deg p) => n le0n.
elim: n le0n p => [|n le0n IHn] p.
+ move=> le_; right; exists X.
  move: (P.deg_eq0 p); rewrite eqz_leq le_ ge0_deg /= => ->>.
  by rewrite dvdp0 /= irredp_deg2 degX.
move/ler_eqVlt=> [eq_|/ltzS/IHn //].
move/ler_eqVlt: le0n => [<<-|lt0n]; [by rewrite eq_|].
right; case: (irreducible_poly p) => [irr_|].
+ by exists p; rewrite irr_ dvdpp.
rewrite /irreducible_poly andaE negb_and -lerNgt negb_forall.
case=> [/P.deg_le1 [c] ->>|[q] /=].
+ move: eq_; rewrite degC ltr_eqF //=.
  by apply/ltr_subl_addr/(ler_lt_trans _ _ _ _ lt0n); case (_ = _).
rewrite !negb_imply neq_ltz ltzE -ler_subr_addr deg_le0 => -[].
case=> [->>|]; [by rewrite dvd0p // => -[->>]; rewrite eqpxx|].
move=> lt1_ [dvdp_ Neqp_]; move/(_ q _): IHn.
+ move: (dvdp_leq _ _ _ dvdp_); [by rewrite -P.deg_eq0 eq_ gtr_eqF // ltzS ltzW|].
  move/dvdp_size_eqp: dvdp_; rewrite Neqp_ /= => neq_.
  case/ler_eqVlt; [by rewrite neq_|]; move/ltzE/ler_subr_addr => le_.
  by apply/(ler_trans _ _ _ le_); rewrite eq_.
rewrite gtr_eqF //= => -[r] [irr_ dvdp__].
exists r. rewrite (dvdp_trans _ _ _ dvdp__ dvdp_) /=.
by move: irr_; rewrite /irreducible_poly.
qed.

op irreducible_dec p qs =
  all irreducible_poly qs /\
  eqp p (BigPoly.PCM.big predT idfun qs).

lemma eqp_irredp_dec p q qs :
  eqp p q =>
  irreducible_dec p qs =>
  irreducible_dec q qs.
proof.
move=> eqp_ [] all_ eqp__; split=> //.
by move: eqp__; apply/eqp_trans; rewrite eqp_sym.
qed.

lemma deg_irredp_dec p qs :
  irreducible_dec p qs =>
  deg p = BIA.big predT (fun q => deg q - 1) qs + 1.
proof.
case=> all_ /eqp_size ->; rewrite deg_prod.
pose f:= predC _; have ->//: all f qs; rewrite /f => {f}.
move: all_; apply/all_imp_in/allP => q mem_ /=.
by rewrite /predC /predI /predT /idfun /=; apply/irredp_neq0.
qed.

lemma degs_irredp_dec p q qs :
  irreducible_dec p qs =>
  q \in qs =>
  deg q \in range 2 (deg p + 1).
proof.
move=> dec_ mem_; rewrite (deg_irredp_dec _ _ dec_); case: dec_ => all_ _.
move/allP/(_ _ mem_)/irredp_poly_deg/ltzE: (all_) => /= le2_.
apply/mem_range; rewrite le2_ -ltr_subl_addr ltzE /=.
rewrite (BIA.big_rem _ _ _ _ mem_) /(predT q) /= -ler_subl_addl /=.
apply/sumr_ge0_seq => r /mem_rem memr _ /=; apply/subr_ge0/ltzW.
by move/allP/(_ _ memr)/irredp_poly_deg: all_.
qed.

lemma irredp_dec_scale c p qs :
  c <> zeror =>
  irreducible_dec p qs <=>
  irreducible_dec (c ** p) qs.
proof.
move=> neqc0; rewrite /irreducible_dec; apply/andb_id2 => //.
move: (eqp_scale p _ neqc0) => eq_; split=> eq__.
+ by move: (eqp_trans _ _ _ eq_ eq__).
by rewrite eqp_sym in eq_; move: (eqp_trans _ _ _ eq_ eq__).
qed.

lemma perm_eq_irredp_dec p qs rs :
  perm_eq qs rs =>
  irreducible_dec p qs =>
  irreducible_dec p rs.
proof.
move=> eq_; rewrite /irreducible_dec (BigPoly.PCM.eq_big_perm _ _ _ _ eq_).
by case=> + -> /=; apply/perm_eq_all.
qed.

lemma irredp_dec_mem p q (qs : poly list) :
  q \in qs =>
  irreducible_dec p qs =>
  irreducible_poly q /\ dvdp q p.
proof.
move=> mem_q [] /allP /(_ _ mem_q) irr_ eqp_.
rewrite irr_ /= (eqp_dvdr _ _ _ eqp_).
by apply/(dvdp_prod _ q) => //; apply/dvdpp.
qed.

lemma irredp_dec_nil p :
  (deg p = 1) <=>
  irreducible_dec p [].
proof. by rewrite /irreducible_dec /= BigPoly.PCM.big_nil deg_eqp. qed.

lemma irredp_dec_cons p q qs :
  (dvdp q p /\ irreducible_poly q /\ irreducible_dec (divp p q) qs) <=>
  irreducible_dec p (q :: qs).
proof.
split=> [[] dvd_ [] irr_ [] all_ eqp_|[] /= [] irr_ all_ eqp_].
+ rewrite /irreducible_dec /= irr_ all_ /=.
  rewrite BigPoly.PCM.big_cons /(predT q) /(idfun q) /=.
  move/(eqp_mull _ q _): eqp_; apply/eqp_trans.
  by rewrite divpKC // eqp_sym eqp_scale lc_expn_scalp_neq0.
rewrite irr_ /=; move: eqp_; rewrite BigPoly.PCM.big_cons.
rewrite /(predT q) /(idfun q) /= => eqp_; rewrite and_impr.
split; [by move/eqp_dvdr: eqp_ => ->; apply/dvdp_mull/dvdpp|].
move=> dvdp_; split=> //; move: eqp_; rewrite eqp_sym.
move/(dvd_eqp_divl _ _ _ dvdp_); rewrite eqp_sym => eqp_.
apply/(eqp_trans _ _ _ eqp_) => {eqp_}; rewrite mulKp.
+ by rewrite -deg_eq0 gtr_eqF // ltzE ltzW //; case: irr_.
by apply/eqp_scale/lc_expn_scalp_neq0.
qed.

lemma irredp_dec0 qs : ! irreducible_dec poly0 qs.
proof.
rewrite /irreducible_dec eqp_sym eqp0 negb_and -implybE => all_.
rewrite -prodf_neq0 /predI /predC /predT /idfun /=; move: all_.
apply/all_imp_in/allP => p mem_p /=; case=> ? _.
by rewrite -deg_eq0 gtr_eqF //; apply/ltzE/ltzW.
qed.

lemma irredp_decC c qs :
  (c <> IDC.zeror /\ qs = []) <=>
  irreducible_dec (polyC c) qs.
proof.
rewrite /irreducible_dec /=; split=> [[neqc0 ->>] /=|].
+ by rewrite BigPoly.PCM.big_nil polyC_eqp1.
case=> all_; case: (c = IDC.zeror) => [->>|neqc0] /=.
+ rewrite eqp_sym eqp0 -prodf_neq0; move: all_.
  apply/all_imp_in/allP => q mem_q /= [lt1 _].
  rewrite /predC /predI /predT /idfun /= -deg_eq0.
  by apply/gtr_eqF/ltzE/ltzW.
move/eqp_size/eq_sym; rewrite degC neqc0 /=.
rewrite deg_prod; pose b:= all _ _; have ->/=: b; rewrite /b => {b}.
+ move: all_; apply/all_imp_in/allP => q mem_q /= [le1_ _].
  rewrite /predC /predI /predT /idfun /= -deg_eq0.
  by apply/gtr_eqF/ltzE/ltzW.
rewrite -subr_eq0 /=; case: qs all_ => // q qs /= [] [lt1_ _] all_.
rewrite Bigint.BIA.big_cons /(predT q) /(\o) /(idfun q) /=.
apply/gtr_eqF/ltzE; rewrite -subr_ge0 addrAC /=; apply/addr_ge0.
+ by apply/subr_ge0; move/ltzE: lt1_.
apply/Bigint.sumr_ge0_seq => p mem_p _.
case/allP/(_ _ mem_p): all_ => le1_ _; rewrite /= /(idfun p) /=.
by apply/subr_ge0/ltzW.
qed.

lemma irredp_dec_deg2 p qs:
  deg p = 2 =>
  (exists q , qs = [q] /\ eqp p q) <=>
  irreducible_dec p qs.
proof.
move=> degp2; split=> [[q] [->> eqp_]|].
+ move/irredp_deg2: degp2; rewrite /irreducible_dec /=.
  move/(irredp_eqp _ _ eqp_) => -> /=.
  by rewrite BigPoly.PCM.big_seq1 /idfun.
case: qs => [/irredp_dec_nil|q qs]; [by rewrite degp2|].
case/irredp_dec_cons=> dvdp_ [] irr_ dec_.
exists q; rewrite eqp_sym; move: (dvdp_size_eqp _ _ dvdp_).
rewrite eqz_leq (dvdp_leq _ _ _ dvdp_); [by rewrite -deg_eq0 degp2|].
rewrite degp2; case: (irr_) => /ltzE -> _ /= /eq_sym /eqT => eqp_.
rewrite eqp_ /=; move: (dvd_eqp_divl _ _ _ dvdp_ eqp_).
rewrite divpp; [by rewrite -deg_eq0; apply/gtr_eqF/ltzE/ltzW; case: irr_|].
rewrite eqp_sym => eqp__; move/(eqp_irredp_dec _ _ _ eqp__): dec_.
by case/irredp_decC.
qed.

lemma irredp_dec_nseq p n q:
  (if 0 < n then irreducible_poly q /\ eqp p (PolyComRing.exp q n) else deg p = 1) <=>
  irreducible_dec p (nseq n q).
proof.
case (0 < n) => [lt0n|/lerNgt len0]; last first.
+ by rewrite nseq0_le //; apply/irredp_dec_nil.
rewrite /irreducible_dec all_nseq lerNgt lt0n /=.
rewrite BigPoly.PCM.big_nseq /(idfun q) /PolyComRing.exp.
by rewrite ltrNge ltzW //= PolyComRing.MulMonoid.iteropE.
qed.

lemma irredp_dec_mem_divp p q (qs : poly list) :
  q \in qs =>
  irreducible_dec p qs =>
  irreducible_dec (divp p q) (rem q qs).
proof.
move=> mem_q; move/perm_to_rem/perm_eq_irredp_dec: (mem_q).
by move=> imp_ /imp_ {imp_} /irredp_dec_cons.
qed.

lemma irredp_dec_dvdp q p qs :
  irreducible_poly q =>
  dvdp q p =>
  irreducible_dec p qs =>
  exists r , r \in qs /\ eqp q r.
proof.
move=> irr_q dvd_qp dec_; elim: qs p dec_ dvd_qp => [|r qs IHqs] p.
+ move=> /irredp_dec_nil eq_ dvd_qp; move: (dvdp_leq _ _ _ dvd_qp).
  - by rewrite -deg_eq0 eq_.
  by rewrite eq_ lerNgt; case: irr_q.
case/irredp_dec_cons => dvd_rp [] irr_r dec_.
move/IHqs: (dec_) =>  {IHqs} IHqs dvd_qp.
move: (Gauss_dvdpor r (divp p r) _ irr_q); rewrite divpKC // dvdpZr.
+ by apply/lc_expn_scalp_neq0.
rewrite dvd_qp eq_sym eqT; case=> [dvd_qr|_ dvd_q_].
+ exists r => //=; split=> // _.
  case: irr_r => _ /(_ _ _ dvd_qr); [|by case].
  by apply/gtr_eqF; case: irr_q.
case/(_ dvd_q_): IHqs => o [] mem_o [] eqp_qo {dec_} dec_.
by exists o; split; [right|split].
qed.

lemma irredp_dec_cat p qs1 qs2 :
  (exists p1 p2 , irreducible_dec p1 qs1 /\ irreducible_dec p2 qs2 /\ eqp p (p1 * p2)) <=>
  irreducible_dec p (qs1 ++ qs2).
proof.
split=> [[p1 p2] [] [] all1 eqp1 [] [] all2 eqp2 eqp_|].
+ split; [by rewrite all_cat|].
  rewrite BigPoly.PCM.big_cat.
  by apply/(eqp_trans _ _ _ eqp_)/eqp_mul.
elim: qs1 qs2 p => [|q1 qs1 IHqs1] qs2 p /=.
+ move=> irr2; exists poly1 p; rewrite -irredp_decC.
  by rewrite oner_neq0 PolyComRing.mul1r eqpxx.
case/irredp_dec_cons => dvdp_ [] irr_ /IHqs1 {IHqs1}.
case=> p1 p2 [] irr1 [] irr2 eq_; exists (q1 * p1) p2.
rewrite -irredp_dec_cons dvdp_mulIl -PolyComRing.mulrA.
rewrite mulKp ?divpKC -?irredp_dec_scale //.
+ by apply/irredp_neq0.
+ by apply/lc_expn_scalp_neq0.
move: eq_; rewrite -(eqp_mul2l q1) => [|eq_].
+ by apply/irredp_neq0.
rewrite (eqp_trans _ _ _ _ eq_) // divpKC // eqp_sym.
by apply/eqp_scale/lc_expn_scalp_neq0.
qed.

lemma irredp_dec_flatten p qss :
  (exists ps ,
     size ps = size qss /\
     all (fun (pqs : poly * poly list) => irreducible_dec pqs.`1 pqs.`2) (zip ps qss) /\
     eqp p (BigPoly.PCM.big predT idfun ps)) <=>
  irreducible_dec p (flatten qss).
proof.
elim: qss p => [|qs qss IHqss] r //=.
+ rewrite flatten_nil -irredp_dec_nil size_poly_eq1.
  split=> [[ps] [] /size_eq0 ->>|?]; [by rewrite BigPoly.PCM.big_nil|].
  by exists []; rewrite BigPoly.PCM.big_nil.
rewrite flatten_cons -irredp_dec_cat; split=> [[[|p ps]]|] //=.
+ by rewrite addrC ltr_eqF // ltzS.
+ case=> /IntID.addrI size_ [] [] dec_ all_; rewrite BigPoly.PCM.big_cons.
  rewrite /(predT p) /(idfun p) /= => eqp_; exists p (divp r p).
  rewrite dec_ divpKC 1?eqp_sym ?eqp_scale ?lc_expn_scalp_neq0 //=.
  - by case: eqp_ => _; apply/dvdp_trans/dvdp_mulIl.
  apply/IHqss; exists ps; rewrite size_ all_ /=.
  move: (dvd_eqp_divl p _ _ _ eqp_); [by apply/dvdp_mulIl|].
  rewrite mulKp; [by apply/negP => ->>; move: dec_; apply/irredp_dec0|].
  rewrite !(eqp_sym (divp _ _)); apply/eqp_trans; rewrite eqp_sym.
  by apply/eqp_scale/lc_expn_scalp_neq0.
case=> p pp; rewrite -IHqss => {IHqss} [] [] dec_ [] [ps] [] size_.
case=> all_ eqp_pp eqp_r; exists (p :: ps); rewrite /= size_ /=.
rewrite dec_ all_ BigPoly.PCM.big_cons /(predT p) /(idfun p) /=.
by apply/(eqp_trans _ _ _ eqp_r)/eqp_mull.
qed.

lemma irredp_decW p :
  p <> poly0 <=>
  exists qs , irreducible_dec p qs.
proof.
split=> [neqp0|[qs] [all_ eqp_]]; last first.
+ apply/negP => ->>; move: eqp_; rewrite eqp_sym eqp0 /=.
  apply/prodf_neq0; move: all_; apply/all_imp_in/allP.
  move=> q mem_q /= [lt1_ _]; rewrite /predC /predI /predT /idfun /=.
  by apply/deg_ge1/ltzW.
move: (P.ge0_deg p) (lerr (P.deg p)); move: {1 3}(P.deg p) => n le0n.
elim: n le0n p neqp0 => [p|n le0n IHn p neqp0].
+ by move/deg_gt0/ltrNge.
move/ler_eqVlt=> [eq_|/ltzS/(IHn _ neqp0) //].
move/ler_eqVlt: le0n => [<<-|lt0n].
+ case/P.deg_eq1: eq_ => ? [neqc0 ->>] {neqp0}.
  by exists []; apply/irredp_decC.
case: (poly1_or_dvdp_i p); [by rewrite eq_ -subr_eq0 /= => ->>|].
case=> q [irr_ dvdp_]; move/(_ (divp p q) _ _): IHn.
+ by rewrite dvdp_div_eq0.
+ rewrite size_divp.
  - rewrite -P.deg_eq0; apply/negP => eq__.
    by move: irr_; rewrite /irreducible_poly eq__.
  rewrite eq_; apply/ler_maxrP; rewrite ltzW //=.
  apply/ltzS/ltr_subl_addr/ltr_subl_addl => /=.
  by apply/subr_gt0; case: irr_.
by case=> qs dec_; exists (q :: qs); apply/irredp_dec_cons.
qed.

lemma irredp_dec_perm_eq p qs1 qs2 :
  irreducible_dec p qs1 =>
  irreducible_dec p qs2 =>
  exists qs,
    size qs1 = size qs /\
    all (fun (p : poly * poly) => eqp p.`1 p.`2) (zip qs1 qs) /\
    perm_eq qs qs2.
proof.
move: (P.ge0_deg p) (lerr (P.deg p)); move: {1 3}(P.deg p) => n le0n.
elim: n le0n p qs1 qs2 => [|n le0n IHn] p qs1 qs2.
+ by move=> /deg_le0 ->>; rewrite irredp_dec0.
move/ler_eqVlt=> [eq_|/ltzS/(IHn _ qs1 qs2) //].
move/ler_eqVlt: le0n => [<<-|lt0n].
+ case/deg_eq1: eq_ => c [neqc0 ->>]; case/irredp_decC => _ ->>.
  by case/irredp_decC => _ ->>; exists [] => /=; apply/perm_eq_nil.
case: qs1 => [|q1 qs1]; [by rewrite -irredp_dec_nil eq_ gtr_eqF // -ltr_subl_addr|].
case/irredp_dec_cons => dvdp1 [] irr1 dec1 dec2.
case: (irredp_dec_dvdp _ _ _ irr1 dvdp1 dec2) => q2 [] mem_q2 eqp_.
move: (irredp_dec_mem_divp _ _ _ mem_q2 dec2) => {dec2} dec2.
move: (dvd_eqp_divr _ _ _ dvdp1 eqp_) => eqp_div.
move/(eqp_irredp_dec _ _ _ eqp_div): dec1 => {eqp_div} dec1.
case/(_ _ _ _ _ dec1 dec2): IHn.
+ move/eqp_size: (dvd_eqp_divr _ _ _ dvdp1 eqp_) => <-.
  rewrite size_divp; [by rewrite -deg_eq0 gtr_eqF // ltzE ltzW //; case: irr1|].
  apply/ler_maxrP; rewrite ltzW //= eq_ opprD /= !addrA -ltzE.
  by apply/ltr_subl_addr/ltr_subl_addl; rewrite addrAC /=; case: irr1.
move=> qs [] eq_size [] all_ perm_eq_; exists (q2 :: qs) => /=.
rewrite eq_size eqp_ all_ /=; move/perm_eq_sym: (perm_to_rem _ _ mem_q2).
by apply/perm_eq_trans/perm_cons.
qed.


(*-----------------------------------------------------------*)
op irreducible_monic_dec p qs =
  irreducible_dec p qs /\ all monic qs.

lemma irredp_monic_decP p qs :
  irreducible_monic_dec p qs <=>
  ( all (predI irreducible_poly monic) qs /\
    p <> poly0 /\
    p = (lc p) ** BigPoly.PCM.big predT idfun qs ).
proof.
rewrite all_predI; split=> [[] dec_ monic_|]; [case: (dec_) => irr_ /eqp_eq <-|].
+ rewrite irr_ monic_ lc_prod /= (BigCf.BCM.eq_big_seq _ (fun _ => IDC.oner)).
  - by move=> q mem_q; rewrite /(\o) /idfun /=; move/allP/(_ _ mem_q): monic_.
  rewrite BigCf.BCM.big1_eq scale1p /=.
  by apply/negP => ->>; move: dec_; apply/irredp_dec0.
case=> [] [] irr_ monic_ [] neq_ eq_; split=> //; split=> //.
by rewrite eq_; apply/eqp_scale; rewrite lc_eq0.
qed.

lemma eqp_irredp_monic_dec p q qs :
  eqp p q =>
  irreducible_monic_dec p qs =>
  irreducible_monic_dec q qs.
proof.
rewrite /irreducible_monic_dec; move/(eqp_irredp_dec _ _ qs).
by move=> imp_ [/imp_] -> ->.
qed.

lemma deg_irredp_monic_dec p qs :
  irreducible_monic_dec p qs =>
  deg p = BIA.big predT (fun q => deg q - 1) qs + 1.
proof. by case=> /deg_irredp_dec. qed.

lemma degs_irredp_monic_dec p q qs :
  irreducible_monic_dec p qs =>
  q \in qs =>
  deg q \in range 2 (deg p + 1).
proof. by case=> /degs_irredp_dec imp_ _; apply/imp_. qed.

lemma irredp_monic_dec_scale c p qs :
  c <> zeror =>
  irreducible_monic_dec p qs <=>
  irreducible_monic_dec (c ** p) qs.
proof.
by move=> neqc0; rewrite /irreducible_monic_dec (irredp_dec_scale _ _ _ neqc0).
qed.

lemma perm_eq_irredp_monic_dec p qs rs :
  perm_eq qs rs =>
  irreducible_monic_dec p qs =>
  irreducible_monic_dec p rs.
proof.
rewrite /irreducible_monic_dec => eq_ [dec_ all_].
move/(perm_eq_irredp_dec p): (eq_) => -> //=.
by move: eq_ all_; apply/perm_eq_all.
qed.

lemma irredp_monic_dec_mem p q (qs : poly list) :
  q \in qs =>
  irreducible_monic_dec p qs =>
  irreducible_poly q /\ monic q /\ dvdp q p.
proof.
move=> mem_ [ ] /(irredp_dec_mem _ _ _ mem_) [] -> ->.
by move/allP/(_ _ mem_).
qed.

lemma irredp_monic_dec_nil p :
  (deg p = 1) <=>
  irreducible_monic_dec p [].
proof. by rewrite /irreducible_monic_dec /= irredp_dec_nil. qed.

lemma irredp_monic_dec_cons p q qs :
  (dvdp q p /\ irreducible_poly q /\ monic q /\ irreducible_monic_dec (divp p q) qs) <=>
  irreducible_monic_dec p (q :: qs).
proof. by rewrite /irreducible_monic_dec -irredp_dec_cons /=; split=> |>. qed.

lemma irredp_monic_dec_cat p qs1 qs2 :
  (exists p1 p2 , irreducible_monic_dec p1 qs1 /\ irreducible_monic_dec p2 qs2 /\ eqp p (p1 * p2)) <=>
  irreducible_monic_dec p (qs1 ++ qs2).
proof.
rewrite /irreducible_monic_dec -irredp_dec_cat; split=> [[p1 p2]|[] [p1 p2]] |>.
+ by move=> irr1 all1 irr2 all2 eq_; rewrite all_cat; split=> //; exists p1 p2.
by move=> irr1 irr2 eq_ /all_cat [] all1 all2; exists p1 p2.
qed.

lemma irredp_monic_dec_flatten p qss :
  (exists ps ,
     size ps = size qss /\
     all (fun (pqs : poly * poly list) => irreducible_monic_dec pqs.`1 pqs.`2) (zip ps qss) /\
     eqp p (BigPoly.PCM.big predT idfun ps)) <=>
  irreducible_monic_dec p (flatten qss).
proof.
rewrite /irreducible_monic_dec -irredp_dec_flatten all_flatten.
split=> [[ps] [] size_ [] all_ eqp_|[] [ps]]; [split|].
+ exists ps; rewrite size_ eqp_ /=; move: all_; apply/all_imp_in.
  by apply/allP => -[].
+ rewrite (all_zip2 (all monic) ps qss) ?size_ //.
  by move: all_; apply/all_imp_in/allP => -[].
case=> size_ [] all_dec eqp_ all_m; exists ps; rewrite size_ eqp_ /=.
move: all_m; rewrite (all_zip2 (all monic) ps qss) ?size_ //; move: all_dec.
pose p1:= (fun (pqs : poly * poly list) => _ pqs.`1 pqs.`2); pose p2:= _ \o _.
move=> all1 all2; move: (all_predI p1 p2 (zip ps qss)); rewrite all1 all2.
by rewrite /p1 /p2 /predI /=; apply/all_imp_in/allP => -[].
qed.

lemma irredp_monic_dec0 qs :
  ! irreducible_monic_dec poly0 qs.
proof. by rewrite /irreducible_monic_dec irredp_dec0. qed.

lemma irreducible_monic_decC c qs :
  (c <> IDC.zeror /\ qs = []) <=>
  irreducible_monic_dec (polyC c) qs.
proof. by rewrite /irreducible_monic_dec -irredp_decC; split=> |>. qed.

lemma irredp_monic_dec_deg2 p qs:
  deg p = 2 =>
  (exists c0 c1 , c1 <> zeror /\ p = c1 ** (X + polyC c0) /\ qs = [X + polyC c0]) <=>
  irreducible_monic_dec p qs.
proof.
move=> deg_; rewrite /irreducible_monic_dec -irredp_dec_deg2 //.
split=> [[] c0 c1 [] neqc10 [] ->> ->> /=|[] [q] [] ->> eqp_ /= m_]; [split|].
+ by exists (X + polyC c0) => /=; rewrite eqp_scale.
+ by rewrite /monic lcDl ?degX ?polyXE // degC; case (_ = _).
exists q.[0] (lc p); move: m_ (eqp_); rewrite /monic => eq_ /eqp_eq.
rewrite lc_eq0 -deg_eq0 deg_ eq_ /= scale1r.
have {eq_} eq_: q = X + polyC q.[0].
+ move/eqp_size: eqp_; rewrite deg_ eq_sym => deg_q.
  apply/poly_eqP => i /ler_eqVlt [<<-|/ltzE/ler_eqVlt [<<-|/ltzE le2i]] /=.
  - by rewrite polyDE polyXE polyCE /= add0r.
  - by rewrite polyDE polyXE polyCE /= addr0; move: eq_; rewrite deg_q.
  rewrite gedeg_coeff ?deg_q // polyDE polyXE polyCE.
  by rewrite gtr_eqF ?ltzE //= add0r gtr_eqF // ltzE ltzW ltzE.
by rewrite -eq_.
qed.

lemma irredp_monic_dec_nseq p n q:
  (if 0 < n then irreducible_poly q /\ monic q /\ eqp p (PolyComRing.exp q n) else deg p = 1) <=>
  irreducible_monic_dec p (nseq n q).
proof. by rewrite /irreducible_monic_dec all_nseq -irredp_dec_nseq lerNgt; case (0 < n). qed.

lemma irredp_monic_dec_mem_divp p q (qs : poly list) :
  q \in qs =>
  irreducible_monic_dec p qs =>
  irreducible_monic_dec (divp p q) (rem q qs).
proof.
rewrite /irreducible_monic_dec => mem_ [] /(irredp_dec_mem_divp _ _ _ mem_).
by move=> -> /=; apply/all_rem.
qed.

lemma irredp_monic_dec_dvdp q p qs :
  irreducible_poly q =>
  monic q =>
  dvdp q p =>
  irreducible_monic_dec p qs =>
  q \in qs.
proof.
move=> irr_ m_ dvdp_ [] dec_ all_.
case: (irredp_dec_dvdp _ _ _ irr_ dvdp_ dec_).
move=> r [] mem_ /eqp_eq; move/allP/(_ _ mem_): all_ m_.
by rewrite /monic => -> ->; rewrite !scale1r => <<-.
qed.

lemma irredp_monic_decW p :
  scaled_monic p <=>
  exists qs , irreducible_monic_dec p qs.
proof.
split=> [[c r] [] neqc0 [] m_ ->>|[qs] [] + m_]; last first.
+ move=> dec_; case: (dec_)=> irr_ /eqp_eq; rewrite lc_prod (BigCf.BCM.eq_big_seq _ (fun _ => oner)).
  - by move=> q mem_; rewrite /(\o) /idfun /=; move/allP/(_ _ mem_): m_; rewrite /monic.
  rewrite BigCf.BCM.big1_eq scale1r => eq_; exists (lc p) (BigPoly.PCM.big predT idfun qs).
  rewrite -eq_ monic_prod /=; [by move: m_; apply/all_imp_in/allP=> q mem_ /=; rewrite /idfun|].
  by rewrite lc_eq0 irredp_decW; exists qs.
move: (irredp_decW r); rewrite -lc_eq0 m_ oner_neq0 /= => -[qs] [] irr_ eqp_.
move/eqp_eq: (eqp_); rewrite m_ scale1r eq_sym lc_prod /= => eq_.
have/scaled_monic_prod all_: scaled_monic (BigPoly.PCM.big predT idfun qs).
+ exists (BigCf.BCM.big predT lc qs) r; move: eq_ => ->; rewrite m_ /=.
  split; [|by congr; apply/BigCf.BCM.eq_big_seq => ? ?; rewrite /(\o) /idfun].
  rewrite -lc_prod lc_eq0 -prodf_neq0; apply/allP => p mem_; rewrite /predI /predC /predT /=.
  by rewrite -deg_eq0; apply/gtr_eqF/ltzE/ltzW; case/allP/(_ _ mem_): irr_.
case: (all_funchoice (fun (p : poly) (cq : coeff * poly) =>
                        let (c, q)= cq in
                        c <> zeror /\ monic q /\ p = c ** q) qs _).
+ move: all_; apply/all_imp_in/allP => q mem_; rewrite /predT /idfun /=.
  by case=> d s [] neqd0 [] m_s ->>; exists (d, s).
move=> f {all_} all_; exists (unzip2 (map f qs)).
apply/irredp_monic_dec_scale => //; split; [split|]; last first.
+ rewrite !all_map; move: all_; apply/all_imp_in/allP => q mem_ /=.
  by rewrite /preim; case: (f q) => ? ?.
+ rewrite !all_map; move: all_; apply/all_imp_in/allP => q mem_ /=.
  rewrite /preim; move: (eq_refl (f q)); case: {2 3 4}(f q) => d s.
  move=> eqf_ /= [] neqd0 [] m_s ->>; move/allP/(_ _ mem_): irr_.
  by rewrite -irredp_poly_scale.
apply/(eqp_trans _ _ _ eqp_); rewrite -map_comp BigPoly.PCM.big_mapT.
apply/eqp_prod/allP => q mem_ ; rewrite /predT /(\o) /idfun /=.
move/allP/(_ _ mem_): all_ => /=; move: (eq_refl (f q)); case: {2 3 4}(f q) => d s.
by move=> {eq_} eq_ /= [] neqd0 [] _ ->>; apply/eqp_scale.
qed.

lemma irredp_monic_dec_perm_eq p qs1 qs2 :
  irreducible_monic_dec p qs1 =>
  irreducible_monic_dec p qs2 =>
  perm_eq qs1 qs2.
proof.
case=> dec1 all1 [] dec2 all2; case: (irredp_dec_perm_eq _ _ _ dec1 dec2).
move=> qs [] eq_ [] all_ perm_; move: (perm_); apply/perm_eq_trans/perm_eq_refl_eq/eq_fromzip.
rewrite eq_ /=; move: all_; apply/all_imp_in/allP => -[] q1 q /mem_zip [] mem_q1 mem_q /= /eqp_eq.
move/perm_eq_sym: perm_ => perm_; move: all1 (perm_eq_all _ _ _ perm_ all2).
by move/allP/(_ _ mem_q1) => + /allP/(_ _ mem_q); rewrite /monic => -> ->; rewrite !scale1r.
qed.

op bundled_irreducible_monic_dec p bqs =
  exists qs ,
    irreducible_monic_dec p qs /\
    perm_eq bqs (bundle qs).

lemma bundled_irredp_monic_decP p bqs :
  bundled_irreducible_monic_dec p bqs <=>
  ( uniq (unzip1 bqs) /\
    all (fun qn => let (q, n) = qn in predI irreducible_poly monic q /\ 0 < n) bqs /\
    p <> poly0 /\
    p = (lc p) ** BigPoly.PCM.big predT (fun qn => let (q, n) = qn in PolyComRing.exp q n) bqs ).
proof.
  split=> [[qs] [] /irredp_monic_decP [] all_ [] neqp0 eqp_ /perm_eq_sym eq_| [] uniq_ [] all_ [] neqp0 eqp_].
  + rewrite neqp0 /=; move/perm_eq_sym: (perm_eq_debundle_bundle qs) => eq__.
    move/(perm_eq_all _ _ _ eq__)/all_debundle: all_ => all_.
    move/(perm_eq_map fst)/perm_eq_sym/perm_eq_uniq: (eq_) => ->.
    rewrite uniq_unzip1_bundle /=.
    move: eqp_; rewrite (BigPoly.PCM.eq_big_perm _ _ _ _ eq__) => {1}-> {eq__}; split.
    - apply/(perm_eq_all _ _ _ eq_).
      move: all_; apply/all_imp_in/allP => -[x n] /mem_bundle [] lt0n <<- /=.
      by rewrite lt0n.
    congr; rewrite BigPoly.PCM.big_debundleT 1?all_map.
    - move: all_; apply/all_imp_in/allP => -[x n] /mem_bundle [] lt0n <<- /=.
      by rewrite lt0n.
    rewrite -(BigPoly.PCM.eq_big_perm _ _ _ _ eq_).
    apply/BigPoly.PCM.eq_big_seq => -[x n] /mem_bundle [] lt0n <<- /=.
    by rewrite /(idfun x).
  exists (debundle bqs); rewrite irredp_monic_decP all_debundle neqp0 /=.
  rewrite perm_eq_sym perm_eq_bundle_debundle //=.
  + by rewrite all_map; move: all_; apply/all_imp_in/allP => -[x n] mem_.
  move: eqp_ => {1}->; split.
  + by move: all_; apply/all_imp_in/allP => -[x n] mem_ /=.
  congr; rewrite BigPoly.PCM.big_debundle.
  + by rewrite all_map; move: all_; apply/all_imp_in/allP => -[x n] mem_.
  by apply/BigPoly.PCM.eq_big_seq => -[q n] mem_; rewrite /idfun.
qed.

lemma eqp_bundled_irredp_monic_dec p q bqs :
  eqp p q =>
  bundled_irreducible_monic_dec p bqs =>
  bundled_irreducible_monic_dec q bqs.
proof.
rewrite /bundled_irreducible_monic_dec => + [qs] [] irr_ ?.
move/(eqp_irredp_monic_dec _ _ qs)/(_ irr_) => ?.
by exists qs.
qed.

lemma bundled_irredp_monic_dec_scale c p bqs :
  c <> zeror =>
  bundled_irreducible_monic_dec p bqs <=>
  bundled_irreducible_monic_dec (c ** p) bqs.
proof.
move=> neqc0; rewrite /bundled_irreducible_monic_dec.
by apply/exists_eq => qs /=; rewrite (irredp_monic_dec_scale _ _ _ neqc0).
qed.

lemma perm_eq_bundled_irredp_monic_dec p bqs brs :
  perm_eq bqs brs =>
  bundled_irreducible_monic_dec p bqs =>
  bundled_irreducible_monic_dec p brs.
proof.
rewrite /bundled_irreducible_monic_dec => eq_ [qs] [] irr_ bundle_.
by exists qs; split=> //; move: bundle_; apply/perm_eq_trans/perm_eq_sym.
qed.

lemma bundled_irredp_monic_dec_mem p q n (bqs : (poly * int) list) :
  (q, n) \in bqs =>
  bundled_irreducible_monic_dec p bqs =>
  irreducible_poly q /\ monic q /\ 0 < n /\ dvdp (PolyComRing.exp q n) p.
proof.
move=> + [qs] [] irr_ /perm_eq_mem eq_; move: eq_ => ->.
case/mem_bundle => lt0n <<-; rewrite lt0n /=.
case/has_count/hasP: lt0n => ? [] mem_; rewrite /pred1 => ->>.
case: (irredp_monic_dec_mem _ _ _ mem_ irr_) => irr_q [] m_ d_.
rewrite irr_q m_ /=; case: irr_ => -[] _ eqp_ _.
move/eqp_dvdr: eqp_ => ->; rewrite -BigPoly.mulr_const_cond.
rewrite (BigPoly.PCM.eq_big _ (pred1 q) _ idfun) //.
by rewrite (BigPoly.PCM.bigEM (pred1 q)) dvdp_mulIl.
qed.

lemma bundled_irredp_monic_dec_nil p :
  (deg p = 1) <=>
  bundled_irreducible_monic_dec p [].
proof.
rewrite /bundled_irreducible_monic_dec /= irredp_monic_dec_nil.
rewrite -irredp_monic_dec_nil; split=> [eq_|[qs] [] irr_ /perm_eq_sym /perm_eq_nil].
+ by exists []; rewrite -irredp_monic_dec_nil bundle_nil.
by move=> /eq_bundle_nil ->>; move/irredp_monic_dec_nil: irr_.
qed.

lemma bundled_irredp_monic_dec_cat p bqs1 bqs2 :
  ( exists p1 p2 ,
      bundled_irreducible_monic_dec p1 bqs1 /\
      bundled_irreducible_monic_dec p2 bqs2 /\
      (forall q , !(q \in unzip1 bqs1 /\ q \in unzip1 bqs2) ) /\
      eqp p (p1 * p2) ) <=>
  bundled_irreducible_monic_dec p (bqs1 ++ bqs2).
proof.
rewrite /bundled_irreducible_monic_dec; split=> [|> p1 p2 qs1 dec1 eq1 qs2 dec2 eq2 Nmem_ eq_| |> qs dec_ eq_].
+ exists (qs1 ++ qs2); rewrite -irredp_monic_dec_cat; split; [by exists p1 p2|].
  apply/perm_eq_sym/(perm_eq_trans _ _ _ (bundle_cat _ _ _)); [|by apply/perm_eq_sym/perm_cat2].
  move=> q; move/(_ q): Nmem_; rewrite !mapP; apply/implybNN => -[] mem1 mem2.
  move: (bundle_assoc qs1 q) => /=; rewrite -mem_count mem1 /= -mem_assoc_uniq.
  - by apply/uniq_unzip1_bundle.
  rewrite -(perm_eq_mem _ _ eq1) => mem1_.
  move: (bundle_assoc qs2 q) => /=; rewrite -mem_count mem2 /= -mem_assoc_uniq.
  - by apply/uniq_unzip1_bundle.
  rewrite -(perm_eq_mem _ _ eq2) => mem2_.
  by split; [exists (q, count (pred1 q) qs1)|exists (q, count (pred1 q) qs2)].
move/debundle_perm_eq: (eq_); rewrite debundle_cat => /perm_eq_sym eq__.
case/irredp_monic_dec_cat: (perm_eq_irredp_monic_dec _ _ _ eq__ dec_).
move=> p1 p2 |> dec1 dec2 eqp_; exists p1 p2; rewrite eqp_ /=.
move/(perm_eq_map fst)/perm_eq_uniq: (eq_).
rewrite map_cat cat_uniq uniq_unzip1_bundle /= => |> u1 Nmem_ u2.
move/(perm_eq_map snd)/perm_eq_sym/perm_eq_all/(_ ((<) 0)): eq_.
rewrite lt0_bundle map_cat all_cat /= => -[] all1 all2; do!split.
+ exists (debundle bqs1); rewrite dec1 perm_eq_sym /=.
  by apply/perm_eq_bundle_debundle.
+ exists (debundle bqs2); rewrite dec2 perm_eq_sym /=.
  by apply/perm_eq_bundle_debundle.
by move=> q; move/hasPn/(_ q): Nmem_ => ?; rewrite negb_and orbC -implybE.
qed.

lemma bundled_irredp_monic_dec0 bqs :
  ! bundled_irreducible_monic_dec poly0 bqs.
proof.
rewrite /bundled_irreducible_monic_dec negb_exists => qs /=.
by rewrite irredp_monic_dec0.
qed.

lemma bundled_irreducible_monic_decC c bqs :
  (c <> IDC.zeror /\ bqs = []) <=>
  bundled_irreducible_monic_dec (polyC c) bqs.
proof.
rewrite /bundled_irreducible_monic_dec; split.
+ by case=> neqc0 ->>; exists []; rewrite bundle_nil -irreducible_monic_decC.
by case=> qs [] /irreducible_monic_decC [] neqc0 ->>; rewrite bundle_nil perm_eq_nil.
qed.

lemma bundled_irredp_monic_dec_deg2 p bqs:
  deg p = 2 =>
  (exists c0 c1 , c1 <> zeror /\ p = c1 ** (X + polyC c0) /\ bqs = [(X + polyC c0, 1)]) <=>
  bundled_irreducible_monic_dec p bqs.
proof.
move=> deg_; rewrite /bundled_irreducible_monic_dec; split.
+ case=> c0 c1 [] neqc10 [] ->> ->>; exists [X + polyC c0].
  rewrite -irredp_monic_dec_deg2 //= -!nseq1 bundle_nseq // nseq1 perm_eq_refl /=.
  by exists c0 c1.
case=> qs []; rewrite -irredp_monic_dec_deg2 // => -[c0 c1] |> neqc10.
by rewrite -nseq1 bundle_nseq // -nseq1 perm_eq_nseq nseq1 => eq_; exists c0 c1.
qed.

lemma bundled_irredp_monic_dec_exp p q n :
  (irreducible_poly q /\ monic q /\ 0 < n /\ eqp p (PolyComRing.exp q n)) <=>
  bundled_irreducible_monic_dec p [(q, n)].
proof.
rewrite /bundled_irreducible_monic_dec; split=> [[] irr_ [] m_ [] lt0n eqp_|[qs] [] dec_].
+ by exists (nseq n q); rewrite -irredp_monic_dec_nseq bundle_nseq lt0n irr_ m_.
case (0 < n) => [lt0n|Nlt0n]; [|by move/perm_eq_mem/(_ (q, n)); rewrite mem_bundle /= Nlt0n].
rewrite -bundle_nseq // perm_eq_bundle perm_eq_sym perm_eq_nseq => ->> /=.
by move: dec_; rewrite -irredp_monic_dec_nseq lt0n.
qed.

lemma bundled_irredp_monic_dec_cons p q n bqs :
  ( dvdp (PolyComRing.exp q n) p /\
    irreducible_poly q /\
    monic q /\
    0 < n /\
    ! (q \in unzip1 bqs) /\
    bundled_irreducible_monic_dec (divp p (PolyComRing.exp q n)) bqs) <=>
  bundled_irreducible_monic_dec p ((q, n) :: bqs).
proof.
rewrite -cat1s -bundled_irredp_monic_dec_cat; split => |>.
+ move=> dvdp_ irr_ m_ lt0n Nmem_ dec_; exists (PolyComRing.exp q n) (divp p (PolyComRing.exp q n)).
  rewrite dec_ /= divpKC // eqp_sym eqp_scale /=; [by apply/lc_expn_scalp_neq0|].
  split; [|by move=> ?; rewrite negb_and -implybE => ->>].
  by rewrite -bundled_irredp_monic_dec_exp eqpxx.
move=> p1 p2 dec1 dec2 Nmem_ eqp_; case/bundled_irredp_monic_dec_exp: dec1.
move=> irr_ [] m_ [lt0n] eqp__; rewrite irr_ m_ lt0n; move: (Nmem_ q) => /= -> /=.
rewrite (eqp_dvdr _ _ _ eqp_) -(eqp_dvdl _ _ _ eqp__) dvdp_mulIl /=.
move: dec2; apply/eqp_bundled_irredp_monic_dec; rewrite eqp_sym.
move: (dvd_eqp_divr p _ _ _ eqp__); [by rewrite (eqp_dvdr _ _ _ eqp_); apply/dvdp_mulIl|].
rewrite eqp_sym => eqp___; apply/(eqp_trans _ _ _ eqp___) => {eqp___}.
move: (dvd_eqp_divl p1 _ _ _ eqp_); [by apply/dvdp_mulIl|rewrite mulKp]; last first.
+ by move=> eqp___; apply/(eqp_trans _ _ _ eqp___)/eqp_scale/lc_expn_scalp_neq0.
apply/negP => ->>; move: eqp__; rewrite eqp_sym eqp0.
by smt(PS.expf_eq0 irredp_neq0).
qed.

lemma bundled_irredp_monic_decW p :
  scaled_monic p <=>
  exists bqs , bundled_irreducible_monic_dec p bqs.
proof.
rewrite irredp_monic_decW; split=> [[qs] dec_|[bqs] [qs] [] dec_ eq_].
+ by exists (bundle qs); exists qs; rewrite perm_eq_refl.
by exists qs.
qed.

lemma bundled_irredp_monic_dec_perm_eq p bqs1 bqs2 :
  bundled_irreducible_monic_dec p bqs1 =>
  bundled_irreducible_monic_dec p bqs2 =>
  perm_eq bqs1 bqs2.
proof.
case=> qs1 [] dec1 eq1 [qs2] [] dec2 eq2.
move/debundle_perm_eq/perm_eq_sym: (eq1) => eq1_.
move/debundle_perm_eq/perm_eq_sym: (eq2) => eq2_.
move/(perm_eq_irredp_monic_dec _ _ _ eq1_): dec1 => {eq1_} dec1.
move/(perm_eq_irredp_monic_dec _ _ _ eq2_): dec2 => {eq2_} dec2.
move: (irredp_monic_dec_perm_eq _ _ _ dec1 dec2) => {dec1 dec2}.
rewrite perm_eq_debundle //.
+ by move/(perm_eq_map fst)/perm_eq_uniq: eq1; rewrite uniq_unzip1_bundle.
+ by move/(perm_eq_map fst)/perm_eq_uniq: eq2; rewrite uniq_unzip1_bundle.
+ by move/(perm_eq_map snd)/perm_eq_sym/perm_eq_all/(_ ((<) 0)): eq1; rewrite lt0_bundle.
by move/(perm_eq_map snd)/perm_eq_sym/perm_eq_all/(_ ((<) 0)): eq2; rewrite lt0_bundle.
qed.

(*TODO: some clone issue somewhere:*)
print IDC.unit.
print CR.unit.

print polyXsubCP.
print root.

lemma degXsubC c : deg (polyNXC c) = 2
  by rewrite degDl degX // -polyCN degC; case: (_ = _).

lemma lcXsubC c : lc (polyNXC c) = oner
  by rewrite lcDl degX ?polyXE //= -polyCN degC; case: (_ = _).

lemma modp_XsubC p c : modp p (polyNXC c) = polyC (peval p c).
proof.
pose q := p - polyC (peval p c); have {1}-> : p = q + polyC (peval p c)
  by rewrite /q PS.addrAC -PS.addrA PS.subrr PS.addr0.
rewrite modpE lcXsubC unitP unitr1 /= expr1z scale1p.
have: root q c by rewrite pevalD pevalN pevalC subrr.
rewrite factor_theorem; move => [? ->].
rewrite rmodp_addl_mul_small ?lcXsubC //.
by rewrite degC degXsubC; case (root _ _).
qed.

lemma coprimep_XsubC p c : coprimep p (polyNXC c) = ! root p c.
proof.
rewrite -coprimep_modl modp_XsubC; case: (peval p c = zeror) => cpP.
- by rewrite cpP coprime0p -deg_eqp degXsubC.
- rewrite -(eqp_coprimepl _ poly1) ?coprime1p //.
  by rewrite eqp_sym -size_poly_eq1 degC cpP.
qed.

lemma coprimep_XsubC2 (a b : coeff) :
  b - a <> zeror => coprimep (polyNXC a) (polyNXC b)
  by rewrite coprimep_XsubC pevalD pevalX pevalN pevalC.

lemma coprimepX p : coprimep p X = ! root p zeror
  by rewrite -(coprimep_XsubC _ zeror) PS.subr0.

lemma eqp_monic p q : monic p => monic q => eqp p q = (p = q).
proof.
move => pP qP; rewrite eq_iff iffE; split => [pqP|->]; rewrite ?eqpxx //.
move: (eqpP p q); rewrite pqP eqT; move => [a b [a_neq0 [b_neq0 abP]]].
apply (PS.mulfI (polyC a)); rewrite ?eq_polyC0 //.
rewrite -!scalepE abP; congr; apply (mulIf oner oner_neq0).
by rewrite -{1}qP -pP -!lcZ_lreg ?lregP // abP.
qed.

lemma dvdp_mul_XsubC p q c :
  dvdp p (polyNXC c * q) = dvdp (if root p c then divp p (polyNXC c) else p) q.
proof.
case: (root p c) => /= [|?]; 2: by rewrite Gauss_dvdpr // coprimep_XsubC.
rewrite root_factor_theorem -eqp_div_XsubC PS.mulrC => {1}->.
by rewrite dvdp_mul2l // -deg_eq0 degXsubC.
qed.

lemma irredp_XsubCP d p :
  irreducible_poly p => dvdp d p => eqp d poly1 \/ eqp d p.
proof.
move=> [_ pP] dvd_dp; case: (eqp d poly1) => //=.
by rewrite -size_poly_eq1 => degP; rewrite (pP d).
qed.

lemma monic_divpE p q : monic q => divp p q = rdivp p q
  by move => monq; rewrite divpE monq unitP unitr1 /= expr1z scale1p.

lemma monic_modpE p q : monic q => modp p q = rmodp p q
  by move => monq; rewrite modpE monq unitP unitr1 /= expr1z scale1p.

lemma monic_scalpE p q : monic q => scalp p q = 0
  by move => monq; rewrite scalpE monq unitP unitr1.

lemma monic_neq0 p : monic p => p <> poly0
  by rewrite -lc_eq0 => ->; rewrite oner_neq0.

lemma monic_divpp p : monic p => divp p p = poly1
  by move => monp; rewrite divpp ?monic_neq0 // monp expr1z.

lemma monic_dvdp_eq p q : monic q => dvdp q p = (p = (divp p q) * q)
  by rewrite dvdp_eq => ->; rewrite expr1z scale1p.

lemma monic_dvdpP p q : monic q => (exists qq, p = qq * q) = dvdp q p.
proof.
move => monq; rewrite eq_iff iffE; split.
- by move => [qq ->]; rewrite dvdp_mulr dvdpp.
- by rewrite dvdp_eq monq expr1z scale1p => ?; exists (divp p q).
qed.

lemma monic_mulpK p q : monic q => divp (p * q) q = p
  by move => monq; rewrite mulpK ?monic_neq0 // monq expr1z scale1p.

lemma monic_mulKp p q : monic q => divp (q * p) q = p
  by move => monq; rewrite mulKp ?monic_neq0 // monq expr1z scale1p.

lemma drop_poly_divp n p : 0 <= n => drop_poly n p = divp p (polyXn n).
proof.
move => n_ge0; rewrite drop_poly_rdivp divpE lcXn //.
by rewrite unitP unitr1 /= expr1z scale1p.
qed.

lemma take_poly_modp n p : 0 <= n => take_poly n p = modp p (polyXn n).
proof.
move => n_ge0; rewrite take_poly_rmodp // modpE lcXn //.
by rewrite unitP unitr1 /= expr1z scale1p.
qed.

lemma ulc_divp_eq d p : IDC.unit (lc d) => p = (divp p d) * d + modp p d
  by rewrite -divp_eq scalpE unitP => -> /=; rewrite expr0 scale1p.

lemma ulc_lc_neq0 p : IDC.unit (lc p) => lc p <> zeror
  by apply contraL => ->; rewrite unitr0.

lemma ulc_edivpP d p q r :
  IDC.unit (lc d) => p = q * d + r => deg r < deg d =>
  q = divp p d /\ r = modp p d.
proof.
move => ulcd ep srd; move: ( ulc_divp_eq d p ulcd); rewrite {1}ep.
have lcdn0 : lc d <> zeror by rewrite ulc_lc_neq0.
rewrite (PS.addrC _ (modp p d)) -PS.subr_eq PS.addrAC -PS.mulrBl => e.
rewrite -e; move: e; rewrite eq_sym -PS.subr_eq -PS.eqr_opp -PS.mulNr !PS.opprB.
case: (q = divp p d) => [->|abs] e /=; 1: by rewrite PS.subrr PS.mul0r PS.add0r.
have hleq /= : deg d <= deg ((divp p d - q) * d).
- rewrite degM_proper; 1: by rewrite mulf_neq0 // lc_eq0 PS.subr_eq0 eq_sym.
  by rewrite addrAC ler_paddl // subz_ge0 deg_ge1 PS.subr_eq0 eq_sym.
suff //= : deg d < deg d; apply (ler_lt_trans _ _ _ hleq); rewrite -e.
apply (ler_lt_trans (max (deg r) (deg (modp p d)))); rewrite ?degB.
case: (deg (modp p d) < deg r) => degP; 1: by rewrite lez_maxl ?ltrW.
by rewrite lez_maxr ?lerNgt // ltn_modp -lc_eq0.
qed.

lemma ulc_divpP d p q r :
  IDC.unit (lc d) => p = q * d + r => deg r < deg d =>
  q = divp p d
  by move => ulcd e degP; move: (ulc_edivpP d p q r); rewrite ulcd -e degP.

lemma ulc_modpP d p q r :
  IDC.unit (lc d) => p = q * d + r => deg r < deg d =>
  r = modp p d
  by move => ulcd e degP; move: (ulc_edivpP d p q r); rewrite ulcd -e degP.

lemma ulc_eqpP p q :
  IDC.unit (lc q) => (exists c, c <> zeror /\ p = c ** q) = eqp p q.
proof.
move => ulcd; have q_nz : q <> poly0 by rewrite -lc_eq0 ulc_lc_neq0.
rewrite eq_iff iffE -{1}eqpP; split.
- by move => [c [c_nz ->]]; exists oner c; rewrite scale1p c_nz oner_neq0.
- move => eq; have p_nz : p <> poly0
    by move: q_nz; rewrite -!eqp0; apply /contra/eqp_trans; rewrite eqp_sym.
  exists (lc p / lc q); rewrite mulf_neq0 ?invr_neq0 ?lc_eq0 //=.
  by rewrite mulrC -scalepA -(eqp_eq _ _ eq) scalepA mulrC divrr // scale1p.
qed.

lemma ulc_dvdp_eq d p : IDC.unit (lc d) => dvdp d p = (p = divp p d * d).
proof.
move => ulcd; rewrite eq_iff iffE; split => [|->]; rewrite /dvdp ?modp_mull //.
by move => modP; move: (ulc_divp_eq d p ulcd); rewrite modP PS.addr0.
qed.

lemma ulc_eqp_eq p q :
  IDC.unit (lc q) => eqp p q => p = (lc p / lc q) ** q.
proof.
move => ulcd /eqp_eq; rewrite mulrC -scalepA => <-.
by rewrite scalepA mulrC divrr // scale1p.
qed.

lemma ulc_modpZl c (d p : poly) :
  IDC.unit (lc d) => modp (c ** p) d = c ** modp p d.
proof.
case: (c = zeror) => [->|c_nz] ulcd; 1: by rewrite !scale0p mod0p.
have e : c ** p = c ** divp p d * d + c ** modp p d
  by rewrite -scalerAl -scalepDr -ulc_divp_eq.
suff s: deg (c ** modp p d) < deg d
  by case: (ulc_edivpP _ _ _ _ ulcd e s) => _ ->.
by rewrite degZ_lreg ?lregP // ltn_modp -lc_eq0 ulc_lc_neq0.
qed.

lemma ulc_divpZl c (d p : poly) :
  IDC.unit (lc d) =>
  divp (c ** p) d = c ** divp p d.
proof.
case: (c = zeror) => [->|c_nz ulcd]; 1: by rewrite !scale0p div0p.
have e : c ** p = c ** divp p d * d + c ** modp p d
  by rewrite -scalerAl -scalepDr -ulc_divp_eq.
suff s: deg (c ** modp p d) < deg d by case (ulc_edivpP _ _ _ _ ulcd e s) => ->.
by rewrite degZ_lreg ?lregP // ltn_modp -lc_eq0 ulc_lc_neq0.
qed.

lemma ulc_eqp_modpl d p q :
  IDC.unit (lc d) => eqp p q =>
  eqp (modp p d) (modp q d).
proof.
rewrite -eqpP. move => ulcd [c1] c2 [c1_nz [c2_nz e]].
by rewrite -eqpP; exists c1 c2; rewrite c1_nz c2_nz /= -!ulc_modpZl // e.
qed.

lemma ulc_eqp_divl d p q :
  IDC.unit (lc d) => eqp p q =>
  eqp (divp p d) (divp q d).
proof.
rewrite -eqpP. move => ulcd [c1] c2 [c1_nz [c2_nz e]].
by rewrite -eqpP; exists c1 c2; rewrite c1_nz c2_nz /= -!ulc_divpZl // e.
qed.

lemma ulc_modpN (d p : poly) : IDC.unit (lc d) => modp (- p) d = - modp p d.
proof.
move => ?; rewrite -PS.mulN1r -polyCN -scalepE.
by rewrite ulc_modpZl // scaleNp scale1p.
qed.

lemma ulc_divpN (d p : poly) : IDC.unit (lc d) => divp (- p) d = - divp p d.
proof.
move => ?; rewrite -PS.mulN1r -polyCN -scalepE.
by rewrite ulc_divpZl // scaleNp scale1p.
qed.

lemma ulc_modpD (d p q : poly) :
  IDC.unit (lc d) =>
  modp (p + q) d = modp p d + modp q d.
proof.
move => ulcd; have e: p + q = (divp p d + divp q d) * d + (modp p d + modp q d)
  by rewrite PS.mulrDl PS.addrACA -!ulc_divp_eq.
suff degP: deg (modp p d + modp q d) < deg d
  by case (ulc_edivpP _ _ _ _ ulcd e degP) => _ ->.
apply (ler_lt_trans _ _ _ (degD (modp p d) (modp q d))).
by rewrite ltr_maxrP !ltn_modp -lc_eq0 ulc_lc_neq0.
qed.

lemma ulc_divpD (d p q : poly) :
  IDC.unit (lc d) =>
  divp (p + q) d = divp p d + divp q d.
proof.
move => ulcd; have e: p + q = (divp p d + divp q d) * d + (modp p d + modp q d)
  by rewrite PS.mulrDl PS.addrACA -!ulc_divp_eq.
suff degP: deg (modp p d + modp q d) < deg d
  by case (ulc_edivpP _ _ _ _ ulcd e degP) => ->.
apply (ler_lt_trans _ _ _ (degD (modp p d) (modp q d))).
by rewrite ltr_maxrP !ltn_modp -lc_eq0 ulc_lc_neq0.
qed.

lemma ulc_mulpK d q : IDC.unit (lc d) => divp (q * d) d = q.
proof.
move: (PS.addr0 (q * d)); rewrite eq_sym => e ulcd.
suff degP: deg poly0 < deg d by case (ulc_edivpP _ _ _ _ ulcd e degP) => <-.
by rewrite deg0 deg_gt0 -lc_eq0 ulc_lc_neq0.
qed.

lemma ulc_mulKp d q : IDC.unit (lc d) => divp (d * q) d = q
  by move => ?; rewrite PS.mulrC ulc_mulpK.

lemma ulc_divp_addl_mul_small d q r :
  IDC.unit (lc d) => deg r < deg d =>
  divp (q * d + r) d = q.
proof.
move => ulcd srd; rewrite ulc_divpD //.
by rewrite (divp_small _ _ srd) PS.addr0 ulc_mulpK.
qed.

lemma ulc_modp_addl_mul_small d q r :
  IDC.unit (lc d) => deg r < deg d =>
  modp (q * d + r) d = r
  by move => ulcd srd; rewrite ulc_modpD // modp_mull PS.add0r modp_small.

lemma ulc_divp_addl_mul d q r :
  IDC.unit (lc d) =>
  divp (q * d + r) d = q + divp r d
  by move => ?; rewrite ulc_divpD ?ulc_mulpK.

lemma ulc_divpp d : IDC.unit (lc d) => divp d d = poly1
  by move => ?; rewrite -{1}PS.mul1r ulc_mulpK.

lemma ulc_leq_trunc_divp d m : IDC.unit (lc d) => deg (divp m d * d) <= deg m.
proof.
case: (divp m d = poly0) => [->|mdP ulcd]; 1: by rewrite PS.mul0r deg0 ge0_deg.
rewrite {2}(ulc_divp_eq d m) // degDl ?ltn_modp //.
rewrite degM_proper ?mulf_neq0 ?(ulc_lc_neq0 d) // ?lc_eq0 //.
by rewrite addrAC ltr_paddl ?subr_ge0 ?deg_ge1 // ltn_modp -lc_eq0 ulc_lc_neq0.
qed.

lemma ulc_dvdpP d p : IDC.unit (lc d) => (exists q, p = q * d) = dvdp d p.
proof.
move => ulcd; rewrite eqboolP iffE {2}ulc_dvdp_eq //; split => [[q ->]|];
by rewrite /dvdp ?modp_mull // => ->; exists (divp p d).
qed.

lemma ulc_divpK d p : IDC.unit (lc d) => dvdp d p => divp p d * d = p
  by move => ?; rewrite ulc_dvdp_eq // => <-.

lemma ulc_divpKC d p : IDC.unit (lc d) => dvdp d p => d * divp p d = p
  by move => 2?; rewrite PS.mulrC ulc_divpK.

lemma ulc_dvdp_eq_div d p q :
  IDC.unit (lc d) => dvdp d p =>
  (q = divp p d) = (q * d = p).
proof.
move => ulcd /(ulc_divpK _ p ulcd) => {2}<-; rewrite eqboolP iffE.
by split => [-> //|]; apply/PS.mulIf; rewrite -lc_eq0 ulc_lc_neq0.
qed.

lemma ulc_dvdp_eq_mul d p q :
  IDC.unit (lc d) => dvdp d p =>
  (p = q * d) = (divp p d = q)
  by move => ulcd dv_d_p; rewrite (eq_sym p) -ulc_dvdp_eq_div // (eq_sym q).

lemma ulc_divp_mulA d p q :
  IDC.unit (lc d) => dvdp d q =>
  p * divp q d = divp (p * q) d.
proof.
move => ulcd hdm; rewrite eq_sym -ulc_dvdp_eq_mul // ?dvdp_mulr //.
by rewrite -PS.mulrA ulc_divpK.
qed.

lemma ulc_divp_mulAC d m n :
  IDC.unit (lc d) => dvdp d m =>
  divp m d * n = divp (m * n) d
  by move => 2?; rewrite PS.mulrC (PS.mulrC m); apply: ulc_divp_mulA.

lemma ulc_divp_mulCA d p q :
  IDC.unit (lc d) => dvdp d p=> dvdp d q =>
  p * divp q d = q * divp p d
  by move=> 3?; rewrite PS.mulrC ulc_divp_mulAC // ulc_divp_mulA.

lemma ulc_modp_mul d p q :
  IDC.unit (lc d) =>
  modp (p * modp q d) d = modp (p * q) d.
proof.
move => ulcd; rewrite {2}(ulc_divp_eq d q) // PS.mulrDr ulc_modpD //.
by rewrite PS.mulrA modp_mull PS.add0r.
qed.

lemma ulc_expp_sub d (m n : int) :
  IDC.unit (lc d) => 0 <= n <= m =>
  PS.exp d (m - n) = divp (PS.exp d m) (PS.exp d n).
proof.
have {3}-> 2? : m = m - n + n by ring.
rewrite (PS.exprD_nneg _ (m - n)) ?ulc_mulpK;
by smt(lcXn_proper unitrX unit_lreg).
qed.

lemma ulc_divp_pmul2l d p q :
  IDC.unit (lc d) => IDC.unit (lc q) =>
  divp (d * p) (d * q) = divp p q.
proof.
move=> uldc uq; rewrite {1}(ulc_divp_eq _ p uq) PS.mulrDr PS.mulrCA.
rewrite ulc_divp_addl_mul ?lcM ?unitrM //.
have dq_nz : d * q <> poly0 by rewrite PS.mulf_eq0 -!lc_eq0 !ulc_lc_neq0.
suff: deg (d * modp p q) < deg (d * q)
  by rewrite ltrNge -divpN0 // negbK => ->; rewrite PS.addr0.
case: (modp p q = poly0) => [->|r_nz]; 1: by rewrite PS.mulr0 deg0 deg_gt0.
by rewrite !degM // ?ltz_add2r ?ltz_add2l ?ltn_modp -lc_eq0 ulc_lc_neq0.
qed.

lemma ulc_divp_pmul2r d p q :
  IDC.unit (lc d) => IDC.unit (lc p) =>
  divp (q * d) (p * d) = divp q p
  by move => 2?; rewrite -!(PS.mulrC d) ulc_divp_pmul2l.

lemma ulc_divp_divl r p q :
  IDC.unit (lc r) => IDC.unit (lc p) =>
  divp (divp q p) r = divp q (p * r).
proof.
move=> ulcr ulcp.
have e : q = divp (divp q p) r * (p * r) + (modp (divp q p) r * p + modp q p).
  rewrite PS.addrA (PS.mulrC p) PS.mulrA -PS.mulrDl.
  by rewrite -ulc_divp_eq -?ulc_divp_eq.
suff s : deg (modp (divp q p) r * p + modp q p) < deg (p * r)
  by case: (ulc_edivpP _ _ _ _ _ e s) => //; rewrite lcM unitrM.
have [r_nz p_nz] : r <> poly0 /\ p <> poly0 by rewrite -!lc_eq0 !ulc_lc_neq0.
case: (modp (divp q p) r = poly0) => [->|modpP].
- rewrite PS.mul0r PS.add0r degM // -addrA.
  by rewrite ltr_paddr ?ltn_modp // subz_ge0 deg_ge1.
- rewrite degDl PS.mulrC !degM //; 2: by rewrite ltz_add2r ltz_add2l ltn_modp.
  by rewrite -addrA ltr_paddr ?ltn_modp // subz_ge0 deg_ge1.
qed.

lemma ulc_divpAC d p q :
  IDC.unit (lc d) => IDC.unit (lc p) =>
  divp (divp q d) p = divp (divp q p) d
  by move => 2?; rewrite !ulc_divp_divl // PS.mulrC.

lemma ulc_modpZr c d p :
  IDC.unit c => IDC.unit (lc d) =>
  modp p (c ** d) = modp p d.
proof.
move => uc ulcd; have e : p = (invr c ** divp p d) * (c ** d) + modp p d.
- rewrite -scalerAl PS.mulrC -scalerAl scalepA mulVr //.
  by rewrite scale1p PS.mulrC -ulc_divp_eq.
suff s : deg (modp p d) < deg (c ** d).
  by rewrite (ulc_modpP _ _ _ _ _ e s) // lcZ_lreg ?unitrM //; apply unit_lreg.
by rewrite degZ_lreg ?ltn_modp -?lc_eq0 ?ulc_lc_neq0 //; apply unit_lreg.
qed.

lemma divpZr c d p :
  IDC.unit c => IDC.unit (lc d) =>
  divp p (c ** d) = IDC.invr c ** divp p d.
proof.
move => uc ulcd; have e : p = (invr c ** divp p d) * (c ** d) + modp p d.
- rewrite -scalerAl PS.mulrC -scalerAl scalepA mulVr //.
  by rewrite scale1p PS.mulrC -ulc_divp_eq.
suff s : deg (modp p d) < deg (c ** d).
  by rewrite (ulc_divpP _ _ _ _ _ e s) // lcZ_lreg ?unitrM //; apply unit_lreg.
by rewrite degZ_lreg ?ltn_modp -?lc_eq0 ?ulc_lc_neq0 //; apply unit_lreg.
qed.

end Idomain.
