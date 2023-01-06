(* -------------------------------------------------------------------- *)
require import AllCore Finite Distr DList List.
require import Poly Ring IntMin Bigalg StdBigop StdOrder.
(*
require (*--*) Subtype.
*)
(*---*) import Bigint IntID IntOrder.

abstract theory RingPseudoDivision.

type coeff, poly.

clone include PolyComRing with
  type coeff <- coeff,
  type poly  <- poly.

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
  by move => ge0_i; apply: degP; smt(coeffE Coeff.oner_neq0 ispolyXn).

lemma lcXn i : 0 <= i => lc (polyXn i) = Coeff.oner
  by smt(coeffE degXn ispolyXn).

lemma coeff_polyXn i j :
  0 <= i => (polyXn i).[j] = if i = j then Coeff.oner else Coeff.zeror
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
have qqP : qq1 * polyC (lc q) = lc q ** qq1 by smt(PolyComRing.mulrC scalepE).
have rP : r1 * polyC (lc q) = lc q ** r1 by smt(PolyComRing.mulrC scalepE).
pose m := polyXn (deg r1 - deg q); suff: deg m <= n /\ deg (m * q) <= n
  by smt(degB degD degZ_le PolyComRing.mulrA scalepE).
suff: deg (m * q) <= n by smt(Coeff.mul1r degM_proper deg_gt0 lcXn lc_eq0).
by rewrite degM_proper; smt(Coeff.mul1r degXn lcXn lc_eq0).
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
rewrite polyDE polyNE PolyComRing.mulrC scalepE -PolyComRing.mulrA -!scalepE.
rewrite !polyZE polyME (BigCf.BCA.big_rem _ _ _ (deg r - deg q)) /predT /=;
  1: by smt(deg_gt0 mem_range).
rewrite coeff_polyXn /= ?Coeff.mul1r ?BigCf.BCA.big1_seq ?Coeff.addr0;
  1, 2: by smt(coeff_polyXn mem_filter mem_range
               Coeff.mul0r range_uniq rem_filter).
by smt(Coeff.mulrC Coeff.mulr0 Coeff.subrr gedeg_coeff).
qed.

lemma ltn_rmodpN0 p q : q <> poly0 => deg (rmodp p q) < deg q
  by smt(ltn_rmodp).

lemma rmodp1 p : rmodp p poly1 = poly0
  by smt(deg1 deg_eq0 ge0_deg ltn_rmodp PolyComRing.oner_neq0).

lemma rmodp_small p q : deg p < deg q => rmodp p q = p.
proof.
rewrite /rmodp /redivp /redivp_rec /=; case: (q = poly0) => //= q_neq0.
by move => degP; rewrite iter_id //= /redivp_rec_it /= degP.
qed.

lemma leq_rmodp m d : deg (rmodp m d) <= deg m
  by smt(ltn_rmodpN0 rmodp0 rmodp_small).

lemma rmodpC p c : c <> Coeff.zeror => rmodp p (polyC c) = poly0
  by smt(degC deg_gt0 ge0_deg ltn_rmodpN0).

lemma rdvdp0 d : rdvdp d poly0 by smt(rmod0p).

lemma rdvd0p n : rdvdp poly0 n = (n = poly0) by smt(rmodp0).

(* rdvd0pP skipped *)

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
   m * polyC (Coeff.exp (lc d) k) = q * d + r).

(* PolyComRing.mulrC used! *)
lemma redivpP m d : redivp_spec m d (redivp m d).
proof.
rewrite /redivp_spec; case: (d = poly0) =>[|d_neq0 /=].
- move => -> /= _; rewrite PolyComRing.mulr0 PolyComRing.add0r.
  by rewrite Coeff.expr0 PolyComRing.mulr1.
case: (d * polyC (lc d) = polyC (lc d) * d) =>[dP /=|]; 2: by smt(ltn_rmodpN0).
suff: let (k, q, r) = redivp m d in
      m * polyC (Coeff.exp (lc d) k) = q * d + r by smt(ltn_rmodpN0).
suff: forall n i i' k qq r,
        i = (k, qq, r, d, deg d, lc d) => deg r <= n =>
        0 <= k => m * polyC (Coeff.exp (lc d) k) = qq * d + r =>
        i' = iter n redivp_rec_it (k, qq, r, d, deg d, lc d) =>
        forall k' qq' r' d' sq' cq', i' = (k', qq', r', d', sq', cq') =>
          m * polyC (Coeff.exp (lc d) k') = qq' * d + r'.
- move => nP; pose i := (0, poly0, m, d, deg d, lc d).
  pose i' := iter (deg m) redivp_rec_it i; move: (nP (deg m) i i').
  have -> : redivp m d = let (k, qq, r, q, sq, cq) = i' in (k, qq, r) by smt().
  suff /# : m * polyC (Coeff.exp (lc d) 0) = poly0 * d + m.
  by smt(Coeff.expr0 PolyComRing.mulr1 PolyComRing.mul0r PolyComRing.add0r).
apply: natind => [|n n_ge0 /= nh i i'' k qq r iP nP k_ge0 mP]; 1: by smt(iter0).
rewrite iterSr // => i''P; pose i' := redivp_rec_it i.
case: (deg r < deg d) => degdrP; 1: by by smt(iter_id).
suff /# : let (k', qq', r', q', sq', cq') = i' in
          deg r' <= n /\ m * polyC (Coeff.exp (lc d) k') = qq' * d + r'.
pose k'  := let (k, qq, r, q, sq, cq) = i' in k.
pose qq' := let (k, qq, r, q, sq, cq) = i' in qq.
pose r'  := let (k, qq, r, q, sq, cq) = i' in r.
pose p := (lc r) ** polyXn (deg r - deg d).
have rP : r' = r  * polyC (lc d) - p * d by smt().
suff: deg r' <= n; 1: suff /# : m * polyC (Coeff.exp (lc d) k') = qq' * d + r'.
- case: (deg r < deg d) => [/#|degP].
  have [-> ->] : k'  = k + 1 /\ qq' = qq * polyC (lc d) + p by smt().
  rewrite rP Coeff.exprSr // polyCM PolyComRing.mulrA mP !PolyComRing.mulrDl.
  rewrite -PolyComRing.mulrA dP PolyComRing.mulrA.
  by smt(PolyComRing.addrCA PolyComRing.addr0 PolyComRing.subrr).
rewrite rP deg_leP // => j jP; rewrite polyDE polyNE.
rewrite PolyComRing.mulrC /p scalepE -PolyComRing.mulrA -!scalepE !polyZE.
rewrite polyME (BigCf.BCA.big_rem _ _ _ (deg r - deg d)) /predT /=;
  1: by smt(deg_gt0 mem_range).
rewrite coeff_polyXn /= ?Coeff.mul1r ?BigCf.BCA.big1_seq ?Coeff.addr0;
  1, 2: by smt(coeff_polyXn mem_filter mem_range
               Coeff.mul0r range_uniq rem_filter).
have {nP} : deg r <= n \/ deg r = n + 1 by smt().
move =>[|nP]; 1: by smt(Coeff.add0r Coeff.mulr0 Coeff.oppr0 gedeg_coeff).
by smt(Coeff.add0r Coeff.mulrC Coeff.mulr0 Coeff.oppr0 Coeff.subrr gedeg_coeff).
qed.

lemma rmodpp p :
  p * (polyC (lc p)) = (polyC (lc p)) * p => rmodp p p = poly0.
proof.
case: (p = poly0) => p_neq0; 1: by smt(rmodp0).
rewrite /rmodp /redivp p_neq0 /= /redivp_rec /redivp_rec_it.
have [d [dP d_ge0]] : exists d, deg p = d + 1 /\ 0 <= d by smt(deg_gt0).
rewrite dP /= iterSr //= dP subrr -addrA subrr addr0 !scalepE polyXn0.
rewrite PolyComRing.mul0r PolyComRing.mulr1 PolyComRing.add0r => ->.
rewrite PolyComRing.subrr /= iter_id; smt(deg0).
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

clone import RingPseudoDivision with
  type coeff <- coeff,
  type poly  <- poly.

(*
op d : poly.

axiom Cdl : d * polyC (lc d) = polyC (lc d) * d.

axiom Rreg : injective (transpose Coeff.( * ) (lc d)).
*)

(* To backport *)
lemma commrX (p q : poly) (n : int) :
  0 <= n => p * q = q * p => p * PolyComRing.exp q n = PolyComRing.exp q n * p.
proof.
move: n; apply: intind; 2: by smt(PolyComRing.exprS PolyComRing.mulrA).
by rewrite /= PolyComRing.expr0 PolyComRing.mulr1 PolyComRing.mul1r.
qed.

lemma rreg_div0 q r d :
  injective (transpose Coeff.( * ) (lc d)) => deg r < deg d =>
  (q * d + r = poly0) = (q = poly0 && r = poly0).
proof.
move => rreg_d lt_r_d; rewrite PolyComRing.addrC PolyComRing.addr_eq0.
case: (q = poly0) => [|q_neq0]; 1: by smt(PolyComRing.mul0r PolyComRing.oppr0).
suff: deg d <= deg (q * d) by smt(degN).
by rewrite degM_proper; smt(deg_ge1 lc_eq0 Coeff.mul0r).
qed.

lemma redivp_eq d q r :
  d * polyC (lc d) = polyC (lc d) * d =>
  injective (transpose Coeff.( * ) (lc d)) =>
  deg r < deg d =>
  let k = rscalp (q * d + r) d in
  let c = polyC (Coeff.exp (lc d) k) in
  redivp (q * d + r) d = (k, q * c, r * c).
proof.
move => Cdl Rreg degrdP; have d_neq0 : d <> poly0 by smt(deg_gt0).
pose k := rscalp (q * d + r) d; pose c := polyC (Coeff.exp (lc d) k).
pose qq := rdivp (q * d + r) d; pose rr := rmodp (q * d + r) d.
suff /# : qq = q * c /\ rr = r * c.
have e : (q * d + r) * c = qq * d + rr by smt(redivpP ltn_rmodpN0).
have e' : q * d * c = q * c * d
  by smt(commrX PolyComRing.mulrA rscalp_ge0 polyCX).
suff: qq = q * c by smt(PolyComRing.addrI PolyComRing.mulrDl).
have {e'} : (qq - q * c) * d = r * c - rr.
- rewrite PolyComRing.mulrBl PolyComRing.subr_eq -e' PolyComRing.addrAC.
  by smt(PolyComRing.addrC PolyComRing.mulrDl PolyComRing.subr_eq).
rewrite -PolyComRing.subr_eq0 PolyComRing.opprB.
suff: deg (rr - r * c) < deg d by smt(rreg_div0 PolyComRing.subr_eq0).
suff: deg (r * c) < deg d by smt(redivpP degB).
by smt(degC degM_le deg0 deg_gt0 PolyComRing.mulr0 PolyComRing.mul0r).
qed.

lemma rdivp_eq d p :
  d * polyC (lc d) = polyC (lc d) * d =>
  p * polyC (Coeff.exp (lc d) (rscalp p d)) = (rdivp p d) * d + (rmodp p d)
  by smt(redivpP).

lemma rreg_lead0 p : injective (transpose Coeff.( * ) (lc p)) => p <> poly0
  by smt(lc_eq0 Coeff.mulr0 Coeff.oner_neq0).

lemma rreg_deg c p :
  injective (transpose Coeff.( * ) c) => deg (p * polyC c) = deg p.
proof.
case: (p = poly0); 1: by smt(PolyComRing.mul0r).
by smt(Coeff.mulr0 Coeff.oner_neq0 degC degM_proper lcC lc_eq0 Coeff.mul0r).
qed.

lemma rreg_polyMC_eq0 c p :
  injective (transpose Coeff.( * ) c) => (p * polyC c = poly0) = (p = poly0)
  by smt(deg_eq0 rreg_deg).

(* TODO: Prove other rreg lemmas using lemmas about lreg *)
lemma rregX c n :
  0 <= n => injective (transpose Coeff.( * ) c) =>
  injective (transpose Coeff.( * ) (Coeff.exp c n))
  by smt(Coeff.lregXn Coeff.mulrC).

lemma eq_rdvdp d k q1 p :
  d * polyC (lc d) = polyC (lc d) * d =>
  injective (transpose Coeff.( * ) (lc d)) =>
  0 <= k => p * polyC (Coeff.exp (lc d) k) = q1 * d => rdvdp d p.
proof.
move => Cdl; pose ld := lc d; pose v := rscalp p d; pose m := max v k.
pose ld_mMv := polyC (Coeff.exp ld (m - v)); move => Rreg k_ge0 he.
pose ld_mMk := polyC (Coeff.exp ld (m - k)).
rewrite /rdvdp -(rreg_polyMC_eq0 _ _ (rregX _ (m - v) _ Rreg)) => [/#|].
suff: ((rdivp p d) * ld_mMv - q1 * ld_mMk) * d + (rmodp p d) * ld_mMv = poly0
  by rewrite rreg_div0 // rreg_deg ?ltn_rmodp ?rreg_lead0 //; smt(rregX).
suff: rdivp p d * ld_mMv * d + rmodp p d * ld_mMv = q1 * ld_mMk * d
  by smt(PolyComRing.addrA PolyComRing.addrC
         PolyComRing.mulrBl PolyComRing.subr_eq0).
have -> : q1 * ld_mMk * d = q1 * d * ld_mMk
  by smt(commrX PolyComRing.mulrA polyCX).
have -> : rdivp p d * ld_mMv * d = rdivp p d * d * ld_mMv
  by smt(commrX PolyComRing.mulrA polyCX).
rewrite -he -PolyComRing.mulrDl -rdivp_eq ?Cdl // -!PolyComRing.mulrA.
by rewrite -!polyCM -!Coeff.exprD_nneg; smt(rscalp_ge0).
qed.

op rdvdp_spec (p q r : poly) (b : bool) : bool =
  (exists k q1, p * polyC (Coeff.exp (lc q) k) = q1 * q) && r = poly0 && b ||
  r = rmodp p q && r <> poly0 && ! b.

lemma rdvdp_eqP d p :
  d * polyC (lc d) = polyC (lc d) * d =>
  injective (transpose Coeff.( * ) (lc d)) =>
  rdvdp_spec p d (rmodp p d) (rdvdp d p).
proof.
case: (rdvdp d p) => [hdvd Cdl|]; 2: by smt(rreg_lead0).
suff /# : p * polyC (Coeff.exp (lc d) (rscalp p d)) = rdivp p d * d.
by rewrite rdivp_eq; smt(PolyComRing.addr0 rmodp_eq0P).
qed.

lemma rdvdp_mull d p :
  d * polyC (lc d) = polyC (lc d) * d =>
  injective (transpose Coeff.( * ) (lc d)) =>
  rdvdp d (p * d)
  by move => 2?; rewrite (eq_rdvdp d 0 p) ?Coeff.expr0 ?PolyComRing.mulr1 /#.

lemma rmodp_mull d p :
  d * polyC (lc d) = polyC (lc d) * d =>
  injective (transpose Coeff.( * ) (lc d)) =>
  rmodp (p * d) d = poly0 by smt(rdvdp_mull).

lemma rmodpp d :
  d * polyC (lc d) = polyC (lc d) * d =>
  injective (transpose Coeff.( * ) (lc d)) =>
  rmodp d d = poly0 by smt(PolyComRing.mul1r rmodp_mull).

lemma mulrI0_rreg (p : poly) :
  (forall q, q * p = poly0 => q = poly0) =>
  injective (transpose PolyComRing.( * ) p).
proof.
move=> reg_p q r qrP; rewrite -PolyComRing.subr_eq0 &(reg_p).
by rewrite PolyComRing.mulrBl; smt(PolyComRing.subrr).
qed.

lemma rreg_lead p :
  injective (transpose Coeff.( * )       (lc p)) =>
  injective (transpose PolyComRing.( * ) p)
  by smt(lcM_proper lc_eq0 mulrI0_rreg Coeff.mul0r).

lemma rdivpp d :
  d * polyC (lc d) = polyC (lc d) * d =>
  injective (transpose Coeff.( * ) (lc d)) =>
  rdivp d d = polyC (Coeff.exp (lc d) (rscalp d d)).
proof.
move => Cdl Rreg; move: (rdivp_eq d d Cdl); rewrite rmodpp ?Cdl //.
by rewrite PolyComRing.addr0 -polyCX ?commrX ?polyCX; smt(rscalp_ge0 rreg_lead).
qed.

lemma rdvdpp d :
  d * polyC (lc d) = polyC (lc d) * d =>
  injective (transpose Coeff.( * ) (lc d)) =>
  rdvdp d d by smt(rmodpp).

lemma rdivpK d p :
  d * polyC (lc d) = polyC (lc d) * d =>
  injective (transpose Coeff.( * ) (lc d)) =>
  rdvdp d p =>
  rdivp p d * d = p * polyC (Coeff.exp (lc d) (rscalp p d))
  by smt(PolyComRing.addr0 rdivp_eq).

end ComRegDivisor.

abstract theory RingMonic.

type coeff, poly.

clone import RingPseudoDivision as RPD with
  type coeff <- coeff,
  type poly  <- poly.

lemma monic_comreg p :
  lc p = Coeff.oner =>
  p * polyC (lc p) = polyC (lc p) * p /\
  injective (transpose Coeff.( * ) (lc p))
  by smt(Coeff.mulr1 PolyComRing.mulr1 PolyComRing.mul1r).

(*
lemma Cdl : d * polyC (lc d) = polyC (lc d) * d by smt(mond monic_comreg).

lemma Rreg : injective (transpose Coeff.( * ) (lc d)) by smt(mond monic_comreg).
*)

clone import ComRegDivisor with
  type   coeff              <- coeff,
  type   poly               <- poly,
  theory RingPseudoDivision <- RPD. (*,
  op     d                  <- d

  proof Cdl  by apply Cdl
  proof Rreg by apply Rreg.
*)

lemma redivp_eq d q r :
  lc d = Coeff.oner =>
  deg r < deg d =>
  let k = rscalp (q * d + r) d in
  redivp (q * d + r) d = (k, q, r)
  by smt(Coeff.expr1z monic_comreg PolyComRing.mulr1 redivp_eq).

lemma rdivp_eq d p : lc d = Coeff.oner => p = rdivp p d * d + rmodp p d
  by smt(Coeff.expr1z monic_comreg PolyComRing.mulr1 rdivp_eq).

lemma rdivpp d : lc d = Coeff.oner => rdivp d d = poly1
  by smt(Coeff.expr1z monic_comreg rdivpp).

lemma rdivp_addl_mul_small d q r :
  lc d = Coeff.oner => deg r < deg d => rdivp (q * d + r) d = q
  by smt(monic_comreg redivp_eq).

lemma rdivp_addl_mul d q r :
  lc d = Coeff.oner => rdivp (q * d + r) d = q + rdivp r d.
proof.
move => mond; move: (monic_comreg d mond) => [Cdl Rreg].
rewrite {1}(rdivp_eq d r) // PolyComRing.addrA -PolyComRing.mulrDl.
by rewrite rdivp_addl_mul_small; smt(ltn_rmodp rreg_lead0).
qed.

lemma rdivpDl d q r :
  lc d = Coeff.oner => rdvdp d q => rdivp (q + r) d = rdivp q d + rdivp r d.
proof.
move => mond; move: (monic_comreg d mond) => [Cdl Rreg].
rewrite {1}(rdivp_eq d r) // PolyComRing.addrA {2}(rdivp_eq d q) // -rmodp_eq0P.
move => ->; rewrite PolyComRing.addr0 -PolyComRing.mulrDl.
by rewrite rdivp_addl_mul_small // ltn_rmodp rreg_lead0 // Rreg.
qed.

lemma rdivpDr d q r :
  lc d = Coeff.oner => rdvdp d r => rdivp (q + r) d = rdivp q d + rdivp r d
  by smt(PolyComRing.addrC rdivpDl).

lemma rdivp_mull d p : lc d = Coeff.oner => rdivp (p * d) d = p
  by smt(PolyComRing.addr0 rdiv0p rdivp_addl_mul).

lemma rmodp_mull d p : lc d = Coeff.oner => rmodp (p * d) d = poly0
  by smt(monic_comreg rmodp_mull).

lemma rmodpp d : lc d = Coeff.oner => rmodp d d = poly0
  by smt(monic_comreg rmodpp).

lemma rmodp_addl_mul_small d q r :
  lc d = Coeff.oner => deg r < deg d => rmodp (q * d + r) d = r
  by smt(monic_comreg redivp_eq).

lemma rmodpD (d p q : poly) :
  lc d = Coeff.oner => rmodp (p + q) d = rmodp p d + rmodp q d.
proof.
move => mond; move: (monic_comreg d mond) => [Cdl Rreg].
rewrite {1}(rdivp_eq d p) // {1}(rdivp_eq d q) // PolyComRing.addrACA.
rewrite  -PolyComRing.mulrDl rmodp_addl_mul_small;
by smt(degD ltn_rmodpN0 rreg_lead0).
qed.

lemma rmodp_mulmr d p q :
  lc d = Coeff.oner => rmodp (p * rmodp q d) d = rmodp (p * q) d.
proof.
move => mond; move: (monic_comreg d mond) => [Cdl Rreg].
rewrite {2}(rdivp_eq d q) // PolyComRing.mulrDr rmodpD //.
by rewrite PolyComRing.mulrA rmodp_mull // PolyComRing.add0r.
qed.

lemma rdvdpp d : lc d = Coeff.oner => rdvdp d d by smt(monic_comreg rdvdpp).

lemma eq_rdvdp d q1 p : lc d = Coeff.oner => p = q1 * d => rdvdp d p
  by smt(eq_rdvdp Coeff.expr1z monic_comreg PolyComRing.mulr1).

lemma rdvdp_mull d p : lc d = Coeff.oner => rdvdp d (p * d)
  by smt(monic_comreg rdvdp_mull).

lemma rdivpK d p : lc d = Coeff.oner => rdvdp d p => (rdivp p d) * d = p
  by smt(PolyComRing.addr0 rdivp_eq rmodp_eq0).

(*
end RingMonic.

abstract theory ExtraMonicDivisor.

type coeff, poly.

clone import RingPseudoDivision as RPD with
  type coeff <- coeff,
  type poly  <- poly.

section Poly1.

clone import RingMonic as RM1 with
  type   coeff              <- coeff,
  type   poly               <- poly,
  theory RPD                <- RPD,
  op     d                  <- poly1

  proof mond  by apply lc1.
*)

lemma rdivp1 p : rdivp p poly1 = p by smt(lc1 PolyComRing.mulr1 rdivp_mull).

(*
end section Poly1.

section PolyXn.

op n : int.

axiom n_ge0 : 0 <= n.

clone import RingMonic as RMXn with
  type   coeff              <- coeff,
  type   poly               <- poly,
  theory RPD                <- RPD,
  op     d                  <- polyXn n

  proof mond  by apply (lcXn _ n_ge0).
*)

op prepolyDrop (k : int) (p : poly) =
  fun i => if 0 <= i < deg p - k /\ 0 <= k then p.[i + k] else Coeff.zeror.

lemma ispolyDrop (k : int) (p : poly) : ispoly (prepolyDrop k p)
  by split => @/prepolyDrop; smt(gedeg_coeff).

op drop_poly k p = to_polyd (prepolyDrop k p).

lemma drop_poly_lt0 n p : n < 0 => drop_poly n p = poly0
  by rewrite poly_eqP => n_lt0 i iP; rewrite coeffE ?ispolyDrop poly0E /#.

op prepolyTake (k : int) (p : poly) =
  fun i => if 0 <= i < k then p.[i] else Coeff.zeror.

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
- rewrite BigCf.BCA.big1_seq; 2: by smt(Coeff.addr0 coeffE ispolyTake).
  rewrite /predT /= => j; rewrite !coeffE; 1, 2: by smt(ispolyDrop ispolyXn).
  by smt(Coeff.mulr0 mem_range).
- have -> : (take_poly n p).[i] = Coeff.zeror by smt(coeffE ispolyTake).
  rewrite Coeff.add0r (BigCf.BCA.big_rem _ _ _ (i - n)); 1: smt(mem_range).
  rewrite /predT /= coeff_polyXn //=; have {3}-> /= : n = i - (i - n) by smt().
  rewrite BigCf.BCA.big1_seq ?Coeff.addr0 ?Coeff.mulr1;
    1: by smt(coeff_polyXn mem_filter mem_range
              Coeff.mulr0 range_uniq rem_filter).
  by rewrite coeffE ?ispolyDrop /prepolyDrop; smt(gedeg_coeff).
qed.

lemma drop_poly_rdivp n p : drop_poly n p = rdivp p (polyXn n).
proof.
case: (0 <= n) => [n_ge0|]; last first.
- suff: n < 0 => polyXn n = poly0 by smt(drop_poly_lt0 rdivp0).
  by smt(coeffE ispolyXn poly0E poly_eqP).
- have mond: lc (polyXn n) = Coeff.oner by apply (lcXn _ n_ge0).
  rewrite -{2}(poly_take_drop n p n_ge0) PolyComRing.addrC rdivp_addl_mul //.
  by rewrite rdivp_small ?PolyComRing.addr0// degXn; smt(size_take_poly).
qed.

lemma take_poly_rmodp n p : 0 <= n => take_poly n p = rmodp p (polyXn n).
proof.
move => n_ge0; have mond: lc (polyXn n) = Coeff.oner by apply (lcXn _ n_ge0).
rewrite -{2}(poly_take_drop n p n_ge0) rmodpD // rmodp_small ?rmodp_mull;
by smt(degXn size_take_poly PolyComRing.addr0).
qed.

(*
end section PolyXn.

section Root.

op x : coeff.

op Xx = polyX - polyC x.

clone import RingMonic as RMXx with
  type   coeff              <- coeff,
  type   poly               <- poly,
  theory RPD                <- RPD,
  op     d                  <- Xx

  proof mond  by rewrite lcDr ?lcX // degN degC degX /#.
*)

op peval' (p : poly) (a : coeff) =
  BigCf.BCA.bigi predT (fun i => Coeff.( * ) p.[i] (Coeff.exp a i)) 0 (deg p).

lemma peval_too_much p a : peval p a = peval' p a.
proof.
rewrite /peval BigCf.BCA.big_int_recr ?ge0_deg /= gedeg_coeff //.
by rewrite Coeff.mul0r Coeff.addr0.
qed.

lemma peval0 x : peval poly0 x = Coeff.zeror
  by rewrite peval_too_much /peval' deg0 range_geq.

lemma pevalC c x : peval (polyC c) x = c.
proof.
admitted.

lemma pevalX x : peval X x = x.
proof.
admitted.

lemma pevalD (p q : poly) x :
  peval (p + q) x = Coeff.( + ) (peval p x) (peval q x).
proof.
pose pf := fun (i : int) => Coeff.( * ) p.[i] (Coeff.exp x i).
have -> : peval p x = BigCf.BCA.bigi predT pf 0 (max (deg p) (deg q)).
  rewrite peval_too_much /peval' eq_sym (BigCf.BCA.big_cat_int (deg p));
  smt(Coeff.addr0 BigCf.BCA.big1_seq gedeg_coeff ge0_deg mem_range Coeff.mul0r).
pose qf := fun (i : int) => Coeff.( * ) q.[i] (Coeff.exp x i).
have -> : peval q x = BigCf.BCA.bigi predT qf 0 (max (deg p) (deg q)).
  rewrite peval_too_much /peval' eq_sym (BigCf.BCA.big_cat_int (deg q));
  smt(Coeff.addr0 BigCf.BCA.big1_seq gedeg_coeff ge0_deg mem_range Coeff.mul0r).
rewrite -BigCf.BCA.big_split peval_too_much /peval' eq_sym.
case: (deg (p + q) < max (deg p) (deg q)); 2: by smt(degD Coeff.mulrDl polyDE).
move => ?; rewrite (BigCf.BCA.big_cat_int (deg (p + q))); 1, 2: by smt(ge0_deg).
have -> : (fun i => Coeff.( * ) (p + q).[i] (Coeff.exp x i)) =
          (fun i => Coeff.( + ) (pf i) (qf i)) by smt(Coeff.mulrDl polyDE).
rewrite -Coeff.subr_eq0 Coeff.addrAC Coeff.subrr Coeff.add0r.
rewrite BigCf.BCA.big1_seq //= => i [_ ]; rewrite mem_range /pf /qf.
by rewrite -Coeff.mulrDl -polyDE; smt(gedeg_coeff Coeff.mul0r).
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
  peval (p * X) x = Coeff.( * ) (peval p x) x.
proof.
rewrite !peval_too_much /peval' BigCf.BCA.big_distrl ?Coeff.mul0r ?Coeff.mulrDl.
case: (p = poly0) => [->|p_neq0]; 1: by smt(deg0 PolyComRing.mul0r range_geq).
rewrite range_ltn; 1: by smt(degM_proper degX ge0_deg lcX lc_eq0 Coeff.mulr1).
have -> : deg (p * X) = deg p + 1
  by rewrite degM_proper ?lcX ?degX // Coeff.mulr1 lc_eq0.
rewrite BigCf.BCA.big_cons /predT /= polyMXE lt0_coeff // Coeff.mul0r.
rewrite Coeff.add0r -/predT (range_add 0 (deg p) 1) BigCf.BCA.big_map.
apply BigCf.BCA.eq_big_seq => i iP /=; rewrite /(\o) -Coeff.mulrA.
by rewrite -Coeff.exprSr ?polyMXE; smt(mem_range).
qed.

lemma pevalZ (c : coeff) (p : poly) x :
  peval (c ** p) x = Coeff.( * ) c (peval p x).
proof.
suff: forall n c p x, deg p <= n =>
        peval (c ** p) x = Coeff.( * ) c (peval p x) by smt(ge0_deg).
apply: natind; 1: by smt(deg_eq0 ge0_deg Coeff.mulr0 scalep0 peval0).
move => /= n n_ge0 nh {c p x} c p x degnpP.
rewrite -{1}(poly_take_drop 1 p) //.
rewrite scalepDr pevalD (scalepE _ (_ * X)) PolyComRing.mulrA -scalepE pevalMX.
have -> : peval (c ** take_poly 1 p) x = Coeff.( * ) c (p.[0]).
- have -> : take_poly 1 p = polyC p.[0]
    by rewrite poly_eqP => i i_ge0; rewrite !coeffE ?ispolyTake ?ispolyC /#.
  rewrite scalepE -polyCM peval_too_much /peval' degC.
  case: (Coeff.( * ) c p.[0] = Coeff.zeror); 1: by smt(BigCf.BCA.big_geq).
  by rewrite rangeS BigCf.BCA.big_seq1 /= Coeff.expr0 Coeff.mulr1 polyCE.
case: (p = poly0) => [->|p_neq0].
- by rewrite poly0E drop_polyn0 // scalep0 !peval0 Coeff.mul0r Coeff.addr0.
- rewrite nh ?deg_drop_poly -?Coeff.mulrA -?Coeff.mulrDr //; 1: by smt().
  rewrite -Coeff.subr_eq0 -Coeff.mulrBr -pevalMX.
  suff -> : p.[0] = peval (take_poly 1 p) x
    by rewrite -pevalD poly_take_drop // Coeff.subrr Coeff.mulr0.
  case: (p.[0] = Coeff.zeror) => [?|p0_neq0]; rewrite peval_too_much /peval'.
  + suff -> : deg (take_poly 1 p) = 0 by rewrite range_geq.
    by rewrite deg_eq0 poly_eqP => i iP; rewrite poly0E coeffE; smt(ispolyTake).
  + have -> : deg (take_poly 1 p) = 1 by apply degP; smt(coeffE ispolyTake).
    by smt(BigCf.BCA.big_seq1 coeffE Coeff.expr0 ispolyTake Coeff.mulr1 rangeS).
qed.

lemma pevalN (p : poly) x : peval (-p) x = Coeff.([ - ]) (peval p x).
proof.
suff -> : -p = (Coeff.([ - ]) Coeff.oner) ** p by rewrite pevalZ Coeff.mulN1r.
by rewrite scaleNp scalepE PolyComRing.mul1r.
qed.

lemma pevalB (p q : poly) x :
  peval (p - q) x = Coeff.( - ) (peval p x) (peval q x) by smt(pevalD pevalN).

lemma pevalM (p q : poly) x :
  peval (p * q) x = Coeff.( * ) (peval p x) (peval q x).
proof.
suff: forall n p q x, deg p <= n =>
        peval (p * q) x = Coeff.( * ) (peval p x) (peval q x) by smt(ge0_deg).
apply: natind; 1: by smt(deg_eq0 ge0_deg Coeff.mul0r PolyComRing.mul0r peval0).
move => /= n n_ge0 nh {p q x} p q x pP; rewrite -{1}(poly_take_drop 1 p) //.
have cP : take_poly 1 p = polyC p.[0]
  by rewrite poly_eqP => i i_ge0; rewrite !coeffE ?ispolyTake ?ispolyC /#.
rewrite cP PolyComRing.mulrDl pevalD -scalepE pevalZ -PolyComRing.mulrA.
rewrite (PolyComRing.mulrC X) nh ?pevalMX; 1: by smt(deg_drop_poly).
rewrite Coeff.mulrCA (Coeff.mulrC (peval q x)) -Coeff.mulrDl -pevalMX.
suff /# : Coeff.( + ) p.[0] (peval (drop_poly 1 p * X) x) = peval p x.
suff -> : p.[0] = peval (take_poly 1 p) x by rewrite -pevalD poly_take_drop.
case: (p.[0] = Coeff.zeror) => p0P; rewrite peval_too_much /peval'.
- suff -> : deg (take_poly 1 p) = 0 by rewrite range_geq.
  by rewrite deg_eq0 poly_eqP => i iP; rewrite poly0E coeffE; smt(ispolyTake).
- have -> : deg (take_poly 1 p) = 1 by apply degP; smt(coeffE ispolyTake).
  by smt(BigCf.BCA.big_seq1 coeffE Coeff.expr0 ispolyTake Coeff.mulr1 rangeS).
qed.

lemma root_XsubC a x : root (X - polyC a) x = (x = a).
proof.
rewrite peval_too_much /peval'; have -> : deg (X - polyC a) = 0 + 1 + 1.
- apply degP; 1, 3: by smt(degB degX degC_le gedeg_coeff).
  by rewrite polyDE polyXE polyNE polyCE /= Coeff.subr0 Coeff.oner_neq0.
rewrite !BigCf.BCA.big_int_recr ?range_geq ?BigCf.BCA.big_nil //=.
rewrite !polyDE !polyXE !polyNE !polyCE /= !Coeff.add0r Coeff.subr0.
rewrite Coeff.expr0 Coeff.expr1 Coeff.mulr1 Coeff.mul1r.
by rewrite Coeff.addrC Coeff.subr_eq0.
qed.

lemma rootMl (p q : poly) r : root p r => root (p * q) r
  by smt(Coeff.mul0r pevalM).

lemma rootMr (p q : poly) r : root q r => root (p * q) r
  by smt(Coeff.mulr0 pevalM).

lemma factor_theorem p r : root p r = exists q, p = q * (polyX - polyC r).
proof.
rewrite eqboolP; split => [prP|]; 2: by smt(rootMr root_XsubC).
search drop_poly.
pose preQ := fun i => if 0 <= i < deg p then peval (drop_poly (i + 1) p) r
                                        else Coeff.zeror.
have isprepolyQ : ispoly preQ by split => @/prepolyTake; smt(gedeg_coeff).
exists (to_polyd preQ); rewrite PolyComRing.mulrBr poly_eqP => i iP.
rewrite polyDE polyNE polyMXE PolyComRing.mulrC -scalepE polyZE !coeffE //.
rewrite /preQ; case: (i < deg p); last first.
- by smt(drop_poly_eq0 gedeg_coeff Coeff.mulr0 peval0 Coeff.subr0).
- move => degipP; have -> /= : i - 1 < deg p by smt().
  case: (i = 0) => [i_eq0|i_neq0]; rewrite ?i_eq0 /=.
  + rewrite Coeff.add0r Coeff.mulrC -pevalMX -Coeff.subr_eq0 Coeff.opprK.
    suff -> : p.[0] = peval (take_poly 1 p) r by smt(pevalD poly_take_drop).
    rewrite peval_too_much /peval'; case: (p.[0] = Coeff.zeror) => p0P.
    * suff -> : deg (take_poly 1 p) = 0 by rewrite range_geq.
      by rewrite deg_eq0 poly_eqP; smt(coeffE ispolyTake poly0E).
    * have -> : deg (take_poly 1 p) = 1 by apply degP; smt(coeffE ispolyTake).
      by smt(BigCf.BCA.big_seq1 coeffE Coeff.expr0
             ispolyTake Coeff.mulr1 rangeS).
  + rewrite iP; have -> /= : 0 <= i - 1 by smt().
    rewrite Coeff.mulrC -pevalMX -pevalB addrC -drop_polyD //.
    rewrite -{1}(poly_take_drop 1 (drop_poly i p)) // -PolyComRing.addrA.
    rewrite PolyComRing.subrr PolyComRing.addr0 peval_too_much /peval'.
    case: (p.[i] = Coeff.zeror) => piP; rewrite ?piP.
    * suff -> : deg (take_poly 1 (drop_poly i p)) = 0 by rewrite range_geq.
      rewrite deg_eq0 poly_eqP; smt(coeffE coef_drop_poly ispolyTake poly0E).
    * have -> : deg (take_poly 1 (drop_poly i p)) = 1
        by apply degP; smt(coeffE coef_drop_poly ispolyTake).
      by smt(BigCf.BCA.big_seq1 coeffE coef_drop_poly
             Coeff.expr0 ispolyTake Coeff.mulr1 rangeS).
qed.

lemma rdvdp_XsubCl_extra_monic x p : rdvdp (polyX - polyC x) p = root p x.
proof.
have mond : lc (polyX - polyC x) = Coeff.oner
  by rewrite lcDr ?lcX // degN degC degX /#.
by smt(PolyComRing.addr0 eq_rdvdp factor_theorem rdivp_eq).
qed.

(*
end section Root.

end ExtraMonicDivisor.
*)

end RingMonic.

abstract theory ComRing.

type coeff, poly.

clone import RingPseudoDivision as RPD with
  type coeff <- coeff,
  type poly  <- poly.

clone import ComRegDivisor as CRD with
  type   coeff              <- coeff,
  type   poly               <- poly,
  theory RingPseudoDivision <- RPD.

clone import RingMonic with
  type   coeff              <- coeff,
  type   poly               <- poly,
  theory RPD                <- RPD,
  theory ComRegDivisor      <- CRD.

op redivp_spec (m d : poly) (i : int * poly * poly) =
  let (k, q, r) = i in
  Coeff.exp (lc d) k ** m = q * d + r && (d <> poly0 => deg r < deg d).

lemma redivpP m d : redivp_spec m d (redivp m d)
  by smt(redivpP scalepE PolyComRing.mulrC).

lemma rdivp_eq d p :
  Coeff.exp (lc d) (rscalp p d) ** p = rdivp p d * d + rmodp p d
  by smt(redivpP).

lemma rdvdp_eqP d p : rdvdp_spec p d (rmodp p d) (rdvdp d p).
proof.
case: (rdvdp d p) => [hdvd|/#]; move: (rmodp_eq0P p d); rewrite {2}hdvd.
move => _; rewrite /rdvdp_spec /=; exists (rscalp p d) (rdivp p d).
by rewrite rdivp_eq 1?PolyComRing.mulrC; smt(PolyComRing.addr0).
qed.

lemma rdvdp_eq q p :
  rdvdp q p = (Coeff.exp (lc q) (rscalp p q) ** p = rdivp p q * q)
  by smt(PolyComRing.addr0 PolyComRing.addrI rdivp_eq).

(* Coeff.unit is a pred and not an op *)
op unit : coeff -> bool.

axiom unitP x : unit x = Coeff.unit x.

op diff_roots (x y : coeff) = unit (Coeff.( - ) x y).
  (* && (Coeff.( * ) x y = Coeff.( * ) y x). *)

op uniq_roots (rs : coeff list) =
  with rs = []      => true
  with rs = c :: cs => all (diff_roots c) cs && uniq_roots cs.

lemma uniq_roots_prod_XsubC p rs :
  all (root p) rs => uniq_roots rs =>
  exists q, p = q * BigPoly.PCM.big predT (fun z => polyX - polyC z) rs.
proof.
elim rs; 1: by exists p; rewrite BigPoly.PCM.big_nil PolyComRing.mulr1.
move => z rs rsP [rpz rprs] [drs urs]; move: (rsP rprs urs) => {rsP} [q pqP].
move: (factor_theorem q z); suff -> : root q z.
- rewrite eq_sym eqT; move => [q' qq'P]; exists q'.
  by rewrite pqP qq'P; rewrite -PolyComRing.mulrA BigPoly.PCM.big_cons.
- move => {rprs urs}; move: drs rpz; rewrite pqP /=; move => {p pqP}.
  elim rs; 1: by rewrite BigPoly.PCM.big_nil PolyComRing.mulr1.
  move => t rs rsP /= [tzP urs].
  rewrite BigPoly.PCM.big_cons /predT /= -/predT PolyComRing.mulrCA pevalM.
  have: peval (X - polyC t) z = Coeff.( - ) z t by smt(pevalB pevalC pevalX).
  by smt(Coeff.mulIr Coeff.mulrC Coeff.mul0r unitP).
qed.

lemma uniq_roots_rdvdp p rs :
  all (root p) rs => uniq_roots rs =>
  rdvdp (BigPoly.PCM.big predT (fun z => polyX - polyC z) rs) p.
proof.
move => har hur; move: (uniq_roots_prod_XsubC _ _ har hur) => [r ->].
pose qf := fun z => polyX - polyC z; pose q := BigPoly.PCM.big predT qf rs.
suff: lc q = Coeff.oner by smt(rdvdp_mull).
suff /# : forall rs, lc (BigPoly.PCM.big predT qf rs) = Coeff.oner.
move => {rs har hur r q} rs; elim rs; 1: by rewrite BigPoly.PCM.big_nil lc1.
move => r rs rsh; rewrite BigPoly.PCM.big_cons.
suff: lc (qf r) = Coeff.oner by smt(lcM_proper Coeff.mulr1 Coeff.oner_neq0).
by rewrite lcDl ?degN ?degC degX ?polyXE /#.
qed.

end ComRing.

abstract theory IdomainDefs.

type coeff, poly.

clone include Poly with
  type coeff <- coeff,
  type poly  <- poly.

clone import ComRing with
  type   coeff <- coeff,
  type   poly  <- poly.

op edivp (p q : poly) =
  let (k, d, r) = RPD.redivp p q in
  if ! unit (lc q) then (k, d, r) else
  let c = IDCoeff.exp (lc q) (- k) in (0, c ** d, c ** r).

op divp p q = let (scal, div, mod) = edivp p q in div.
op modp p q = let (scal, div, mod) = edivp p q in mod.
op scalp p q = let (scal, div, mod) = edivp p q in scal.
op dvdp p q = (RPD.rmodp q p = poly0).
op eqp p q = (dvdp p q) && (dvdp q p).

end IdomainDefs.

abstract theory WeakIdomain.

type coeff, poly.

clone import IdomainDefs as IDD with
  type   coeff <- coeff,
  type   poly  <- poly.

clone import IDD.ComRing as CR.

lemma edivp_def p q : edivp p q = (scalp p q, divp p q, modp p q) by smt().

lemma edivp_redivp p q : ! IDCoeff.unit (lc q) => edivp p q = RPD.redivp p q.
proof.
admitted.

lemma divpE p q :
  divp p q = if IDCoeff.unit (lc q)
    then IDCoeff.exp (lc q) (- RPD.rscalp p q) ** RPD.rdivp p q
    else RPD.rdivp p q.
proof.
admitted.

lemma modpE p q :
  modp p q = if IDCoeff.unit (lc q)
    then IDCoeff.exp (lc q) (- RPD.rscalp p q) ** RPD.rmodp p q
    else RPD.rmodp p q.
proof.
admitted.

lemma scalpE p q :
  scalp p q = if IDCoeff.unit (lc q) then 0 else RPD.rscalp p q.
proof.
admitted.

lemma dvdpE p q : dvdp p q = RPD.rdvdp p q.
proof.
admitted.

lemma lc_expn_scalp_neq0 p q : IDCoeff.exp (lc q) (scalp p q) <> IDCoeff.zeror.
proof.
admitted.

op edivp_spec (m d : poly) (i : int * poly * poly) (b : bool) =
  let (k, q, r) = i in
  IDCoeff.exp (lc d) k ** m = q * d + r && ! unit (lc d) &&
  (d <> poly0 => deg r < deg d) && ! b ||
  m = q * d + r && unit (lc d) && (d <> poly0 => deg r < deg d) && k = 0 && b.

lemma edivpP m d : edivp_spec m d (edivp m d) (IDCoeff.unit (lc d)).
proof.
admitted.

lemma edivp_eq d q r : deg r < deg d => IDCoeff.unit (lc d) =>
  edivp (q * d + r) d = (0, q, r).
proof.
admitted.

lemma divp_eq p q :
  IDCoeff.exp (lc q) (scalp p q) ** p = (divp p q) * q + (modp p q).
proof.
admitted.

lemma dvdp_eq q p :
  dvdp q p = (IDCoeff.exp (lc q) (scalp p q) ** p = (divp p q) * q).
proof.
admitted.

lemma divpK d p : dvdp d p => divp p d * d = IDCoeff.exp (lc d) (scalp p d) ** p.
proof.
admitted.

lemma divpKC d p :
  dvdp d p => d * (divp p d) = IDCoeff.exp (lc d) (scalp p d) ** p.
proof.
admitted.

(* dvdpP skipped *)

lemma mulpK p q :
  q <> poly0 => divp (p * q) q = IDCoeff.exp (lc q) (scalp (p * q) q) ** p.
proof.
admitted.

lemma mulKp p q :
  q <> poly0 => divp (q * p) q = IDCoeff.exp (lc q) (scalp (p * q) q) ** p.
proof.
admitted.

lemma divpp p : p <> poly0 => divp p p = polyC (IDCoeff.exp (lc p) (scalp p p)).
proof.
admitted.

end WeakIdomain.

abstract theory CommonIdomain.

type coeff, poly.

clone import WeakIdomain as WID with
  type   coeff <- coeff,
  type   poly  <- poly.

clone import WID.IDD as IDD.

lemma scalp0 p : scalp p poly0 = 0.
proof.
admitted.

lemma divp_small p q : deg p < deg q => divp p q = poly0.
proof.
admitted.

lemma leq_divp p q : deg (divp p q) <= deg p.
proof.
admitted.

lemma div0p p : divp poly0 p = poly0.
proof.
admitted.

lemma divp0 p : divp p poly0 = poly0.
proof.
admitted.

lemma divp1 m : divp m poly1 = m.
proof.
admitted.

lemma modp0 p : modp p poly0 = p.
proof.
admitted.

lemma mod0p p : modp poly0 p = poly0.
proof.
admitted.

lemma modp1 p : modp p poly1 = poly0.
proof.
admitted.

lemma modp_small p q : deg p < deg q => modp p q = p.
proof.
admitted.

lemma modpC p c : c <> IDCoeff.zeror => modp p (polyC c) = poly0.
proof.
admitted.

lemma modp_mull (p q : poly) : modp (p * q) q = poly0.
proof.
admitted.

lemma modp_mulr (d p : poly) : modp (d * p) d = poly0.
proof.
admitted.

lemma modpp d : modp d d = poly0.
proof.
admitted.

lemma ltn_modp p q : (deg (modp p q) < deg q) = (q <> poly0).
proof.
admitted.

lemma ltn_divpl d q p : d <> poly0 =>
  (deg (divp q d) < deg p) = (deg q < deg (p * d)).
proof.
admitted.

lemma leq_divpr d p q : d <> poly0 =>
  (deg p <= deg (divp q d)) = (deg (p * d) <= deg q).
proof.
admitted.

lemma divpN0 d p : d <> poly0 => (divp p d <> poly0) = (deg d <= deg p).
proof.
admitted.

lemma size_divp p q : q <> poly0 => deg (divp p q) = deg p - deg q - 1.
proof.
admitted.

lemma ltn_modpN0 p q : q <> poly0 => deg (modp p q) < deg q.
proof.
admitted.

lemma modp_mod p q : modp (modp p q) q = modp p q.
proof.
admitted.

lemma leq_modp m d : deg (modp m d) <= deg m.
proof.
admitted.

lemma dvdp0 d : dvdp d poly0.
proof.
admitted.

lemma dvd0p p : (dvdp poly0 p) = (p = poly0).
proof.
admitted.

(* dvd0pP skipped *)

lemma dvdpN0 p q : dvdp p q => q <> poly0 => p <> poly0.
proof.
admitted.

lemma dvdp1 d : dvdp d poly1 = (deg d = 1).
proof.
admitted.

lemma dvd1p m : dvdp poly1 m.
proof.
admitted.

lemma gtNdvdp p q : p <> poly0 => deg p < deg q => dvdp q p = false.
proof.
admitted.

(* modp_eq0P skipped *)

lemma modp_eq0 p q : dvdp q p => modp p q = poly0.
proof.
admitted.

lemma leq_divpl d p q :
  dvdp d p => (deg (divp p d) <= deg q) = (deg p <= deg (q * d)).
proof.
admitted.

lemma dvdp_leq p q : q <> poly0 => dvdp p q => deg p <= deg q.
proof.
admitted.

lemma eq_dvdp c (quo q p : poly) :
  c <> IDCoeff.zeror => c ** p = quo * q => dvdp q p.
proof.
admitted.

lemma dvdpp d : dvdp d d.
proof.
admitted.

lemma divp_dvd p q : dvdp p q => dvdp (divp q p) q.
proof.
admitted.

lemma dvdp_mull m d n : dvdp d n => dvdp d (m * n).
proof.
admitted.

lemma dvdp_mulr n d m : dvdp d m => dvdp d (m * n).
proof.
admitted.

lemma dvdp_mul d1 d2 m1 m2 :
  dvdp d1 m1 => dvdp d2 m2 => dvdp (d1 * d2) (m1 * m2).
proof.
admitted.

lemma dvdp_addr m d n : dvdp d m => dvdp d (m + n) = dvdp d n.
proof.
admitted.

lemma dvdp_addl n d m : dvdp d n => dvdp d (m + n) = dvdp d m.
proof.
admitted.

lemma dvdp_add d m n : dvdp d m => dvdp d n => dvdp d (m + n).
proof.
admitted.

lemma dvdp_add_eq (d m n : poly) : dvdp d (m + n) => dvdp d m = dvdp d n.
proof.
admitted.

lemma dvdp_subr d m n : dvdp d m => dvdp d (m - n) = dvdp d n.
proof.
admitted.

lemma dvdp_subl d m n : dvdp d n => dvdp d (m - n) = dvdp d m.
proof.
admitted.

lemma dvdp_sub d m n : dvdp d m => dvdp d n => dvdp d (m - n).
proof.
admitted.

lemma dvdp_mod d n m : dvdp d n => dvdp d m = dvdp d (modp m n).
proof.
admitted.

lemma dvdp_trans : transitive dvdp.
proof.
admitted.

lemma dvdp_mulIl (p q : poly) : dvdp p (p * q).
proof.
admitted.

lemma dvdp_mulIr (p q : poly) : dvdp q (p * q).
proof.
admitted.

lemma dvdp_mul2r r p q : r <> poly0 => dvdp (p * r) (q * r) = dvdp p q.
proof.
admitted.

lemma dvdp_mul2l r p q: r <> poly0 => dvdp (r * p) (r * q) = dvdp p q.
proof.
admitted.

lemma ltn_divpr d p q :
  dvdp d q => deg p < deg (divp q d) = (deg (p * d) < deg q).
proof.
admitted.

lemma dvdp_exp d k p : 0 < k => dvdp d p => dvdp d (PolyComRing.exp p k).
proof.
admitted.

lemma dvdp_exp2l d (k l : int) :
  k <= l => dvdp (PolyComRing.exp d k) (PolyComRing.exp d l).
proof.
admitted.

lemma dvdp_Pexp2l d k l :
  1 < deg d => dvdp (PolyComRing.exp d k) (PolyComRing.exp d l) = (k <= l).
proof.
admitted.

lemma dvdp_exp2r p q k :
  dvdp p q => dvdp (PolyComRing.exp p k) (PolyComRing.exp q k).
proof.
admitted.

lemma dvdp_exp_sub p q k l: p <> poly0 =>
  dvdp (PolyComRing.exp p k) (q * (PolyComRing.exp p l)) =
  dvdp (PolyComRing.exp p (k - l)) q.
proof.
admitted.

lemma dvdp_XsubCl p x : dvdp (polyX - polyC x) p = root p x.
proof.
admitted.

(* polyXsubCP skipped *)

lemma eqp_div_XsubC p c :
  (p = divp p (polyX - polyC c) * (polyX - polyC c)) = dvdp (polyX - polyC c) p.
proof.
admitted.

lemma root_factor_theorem p x : root p x = dvdp (polyX - polyC x) p.
proof.
admitted.

lemma uniq_roots_dvdp p rs : all (root p) rs => uniq rs =>
  dvdp (BigPoly.PCM.big predT (fun z => polyX - polyC z) rs) p.
proof.
admitted.

lemma root_bigmul x ps :
  ! root (BigPoly.PCM.big predT idfun ps) x = all (fun p => ! root p x) ps.
proof.
admitted.

(* eqpP skipped *)

lemma eqp_eq p q: eqp p q => (lc q) ** p = (lc p) ** q.
proof.
admitted.

lemma eqpxx : reflexive eqp.
proof.
admitted.

lemma eqp_sym : symmetric eqp by smt().

lemma eqp_trans : transitive eqp.
proof.
admitted.

lemma eqp_ltrans : left_transitive eqp.
proof.
admitted.

lemma eqp_rtrans : right_transitive eqp.
proof.
admitted.

lemma eqp0 p : eqp p poly0 = (p = poly0).
proof.
admitted.

lemma eqp01 : eqp poly0 poly1 = false.
proof.
admitted.

lemma eqp_scale p c : c <> IDCoeff.zeror => eqp (c ** p) p.
proof.
admitted.

lemma eqp_size p q : eqp p q => deg p = deg q.
proof.
admitted.

lemma size_poly_eq1 p : (deg p = 1) = eqp p poly1.
proof.
admitted.

lemma polyXsubC_eqp1 x : eqp (polyX - polyC x) poly1 = false.
proof.
admitted.

lemma dvdp_eqp1 p q : dvdp p q => eqp q poly1 => eqp p poly1.
proof.
admitted.

lemma eqp_dvdr q p d: eqp p q => dvdp d p = dvdp d q.
proof.
admitted.

lemma eqp_dvdl d2 d1 p : eqp d1 d2 => dvdp d1 p = dvdp d2 p.
proof.
admitted.

lemma dvdpZr c m n : c <> IDCoeff.zeror => dvdp m (c ** n) = dvdp m n.
proof.
admitted.

lemma dvdpZl c m n : c <> IDCoeff.zeror => dvdp (c ** m) n = dvdp m n.
proof.
admitted.

lemma dvdpNl (d p : poly) : dvdp (- d) p = dvdp d p.
proof.
admitted.

lemma dvdpNr (d p : poly) : dvdp d (- p) = dvdp d p.
proof.
admitted.

lemma eqp_mul2r r p q : r <> poly0 => eqp (p * r) (q * r) = eqp p q.
proof.
admitted.

lemma eqp_mul2l r p q: r <> poly0 => eqp (r * p) (r * q) = eqp p q.
proof.
admitted.

lemma eqp_mull r p q: eqp q r => eqp (p * q) (p * r).
proof.
admitted.

lemma eqp_mulr q p r : eqp p q => eqp (p * r) (q * r).
proof.
admitted.

lemma eqp_exp p q k :
  eqp p q => eqp (PolyComRing.exp p k) (PolyComRing.exp q k).
proof.
admitted.

lemma polyC_eqp1 c : eqp (polyC c) poly1 = (c <> IDCoeff.zeror).
proof.
admitted.

lemma dvdUp d p: eqp d poly1 => dvdp d p.
proof.
admitted.

lemma dvdp_size_eqp p q : dvdp p q => (deg p = deg q) = eqp p q.
proof.
admitted.

lemma eqp_root p q : eqp p q => root p = root q.
proof.
admitted.

lemma eqp_rmod_mod p q : eqp (IDD.ComRing.RPD.rmodp p q) (modp p q).
proof.
admitted.

lemma eqp_rdiv_div p q : eqp (IDD.ComRing.RPD.rdivp p q) (divp p q).
proof.
admitted.

lemma dvd_eqp_divl d p q :
  dvdp d q => eqp p q => eqp (divp p d) (divp q d).
proof.
admitted.

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
  let (ppp, qqq) = iter (deg pp) gcdp_rec_it (pp, qq) in qq.

lemma gcd0p : left_id poly0 gcdp.
proof.
admitted.

lemma gcdp0 : right_id poly0 gcdp.
proof.
admitted.

lemma gcdpE p q :
  gcdp p q = if deg p < deg q
    then gcdp (modp q p) p else gcdp (modp p q) q.
proof.
admitted.

lemma size_gcd1p p : deg (gcdp poly1 p) = 1.
proof.
admitted.

lemma size_gcdp1 p : deg (gcdp p poly1) = 1.
proof.
admitted.

lemma gcdpp : idempotent gcdp.
proof.
admitted.

lemma dvdp_gcdlr p q : dvdp (gcdp p q) p && dvdp (gcdp p q) q.
proof.
admitted.

lemma dvdp_gcdl p q : dvdp (gcdp p q) p.
proof.
admitted.

lemma dvdp_gcdr p q : dvdp (gcdp p q) q.
proof.
admitted.

lemma leq_gcdpl p q : p <> poly0 => deg (gcdp p q) <= deg p.
proof.
admitted.

lemma leq_gcdpr p q : q <> poly0 => deg (gcdp p q) <= deg q.
proof.
admitted.

lemma dvdp_gcd p m n : dvdp p (gcdp m n) = dvdp p m && dvdp p n.
proof.
admitted.

lemma gcdpC p q : eqp (gcdp p q) (gcdp q p).
proof.
admitted.

lemma gcd1p p : eqp (gcdp poly1 p) poly1.
proof.
admitted.

lemma gcdp1 p : eqp (gcdp p poly1) poly1.
proof.
admitted.

lemma gcdp_addl_mul (p q r : poly) : eqp (gcdp r (p * r + q)) (gcdp r q).
proof.
admitted.

lemma gcdp_addl (m n : poly) : eqp (gcdp m (m + n)) (gcdp m n).
proof.
admitted.

lemma gcdp_addr (m n : poly) : eqp (gcdp m (n + m)) (gcdp m n).
proof.
admitted.

lemma gcdp_mull (m n : poly) : eqp (gcdp n (m * n)) n.
proof.
admitted.

lemma gcdp_mulr (m n : poly) : eqp (gcdp n (n * m)) n.
proof.
admitted.

lemma gcdp_scalel c m n :
  c <> IDCoeff.zeror => eqp (gcdp (c ** m) n) (gcdp m n).
proof.
admitted.

lemma gcdp_scaler c m n :
  c <> IDCoeff.zeror => eqp (gcdp m (c ** n)) (gcdp m n).
proof.
admitted.

lemma dvdp_gcd_idl m n : dvdp m n => eqp (gcdp m n) m.
proof.
admitted.

lemma dvdp_gcd_idr m n : dvdp n m => eqp (gcdp m n) n.
proof.
admitted.

lemma gcdp_exp p k l :
  eqp (gcdp (PolyComRing.exp p k) (PolyComRing.exp p l))
      (PolyComRing.exp p (min k l)).
proof.
admitted.

lemma gcdp_eq0 p q : (gcdp p q = poly0) = (p = poly0) && (q = poly0).
proof.
admitted.

lemma eqp_gcdr p q r : eqp q r => eqp (gcdp p q) (gcdp p r).
proof.
admitted.

lemma eqp_gcdl r p q : eqp p q => eqp (gcdp p r) (gcdp q r).
proof.
admitted.

lemma eqp_gcd p1 p2 q1 q2 :
  eqp p1 p2 => eqp q1 q2 => eqp (gcdp p1 q1) (gcdp p2 q2).
proof.
admitted.

lemma eqp_rgcd_gcd p q : eqp (IDD.ComRing.RPD.rgcdp p q) (gcdp p q).
proof.
admitted.

lemma gcdp_modl m n : eqp (gcdp (modp m n) n) (gcdp m n).
proof.
admitted.

lemma gcdp_modr m n : eqp (gcdp m (modp n m)) (gcdp m n).
proof.
admitted.

lemma gcdp_def d m n :
  dvdp d m => dvdp d n => (forall d', dvdp d' m => dvdp d' n => dvdp d' d) =>
  eqp (gcdp m n) d.
proof.
admitted.

op coprimep p q = deg (gcdp p q) = 1.

lemma coprimep_size_gcd p q : coprimep p q => deg (gcdp p q) = 1.
proof.
admitted.

lemma coprimep_def p q : coprimep p q = (deg (gcdp p q) = 1).
proof.
admitted.

lemma coprimepZl c m n :
  c <> IDCoeff.zeror => coprimep (c ** m) n = coprimep m n.
proof.
admitted.

lemma coprimepZr c m n:
  c <> IDCoeff.zeror => coprimep m (c ** n) = coprimep m n.
proof.
admitted.

lemma coprimepp p : coprimep p p = (deg p = 1).
proof.
admitted.

lemma gcdp_eqp1 p q : eqp (gcdp p q) poly1 = coprimep p q.
proof.
admitted.

lemma coprimep_sym p q : coprimep p q = coprimep q p.
proof.
admitted.

lemma coprime1p p : coprimep poly1 p.
proof.
admitted.

lemma coprimep1 p : coprimep p poly1.
proof.
admitted.

lemma coprimep0 p : coprimep p poly0 = eqp p poly1.
proof.
admitted.

lemma coprime0p p : coprimep poly0 p = eqp p poly1.
proof.
admitted.

(* coprimepP and coprimepPn skipped *)

lemma coprimep_dvdl q p r : dvdp r q => coprimep p q => coprimep p r.
proof.
admitted.

lemma coprimep_dvdr p q r : dvdp r p => coprimep p q => coprimep r q.
proof.
admitted.

lemma coprimep_modl p q : coprimep (modp p q) q = coprimep p q.
proof.
admitted.

lemma coprimep_modr q p : coprimep q (modp p q) = coprimep q p.
proof.
admitted.

lemma rcoprimep_coprimep q p : IDD.ComRing.RPD.rcoprimep q p = coprimep q p.
proof.
admitted.

lemma eqp_coprimepr p q r : eqp q r => coprimep p q = coprimep p r.
proof.
admitted.

lemma eqp_coprimepl p q r : eqp q r => coprimep q p = coprimep r p.
proof.
admitted.

(* To define *)
op egcdp_rec ((* i *) p q : poly (* * poly *)) (k : int) : poly * poly.

op egcdp p q =
  if deg q <= deg p then egcdp_rec p q (deg q)
    else let (u, v) = egcdp_rec q p (deg p) in (v, u).

lemma egcdp0 p : egcdp p poly0 = (poly1, poly0).
proof.
admitted.

lemma egcdp_recP :
  forall k p q, q <> poly0 => deg q <= k => deg q <= deg p =>
  let (u, v) = (egcdp_rec p q k) in
  deg u <= deg v && deg v <= deg p && eqp (gcdp p q) (u * p + v * q).
proof.
admitted.

lemma egcdpP p q :
  p <> poly0 => q <> poly0 => forall u v, (u, v) = egcdp p q =>
  deg u <= deg q && deg v <= deg p && eqp (gcdp p q) (u * p + v * q).
proof.
admitted.

lemma egcdpE p q :
  forall u v, (u, v) = egcdp p q => eqp (gcdp p q) (u * p + v * q).
proof.
admitted.

lemma Bezoutp (p q : poly) : exists u v, eqp (u * p + v * q) (gcdp p q).
proof.
admitted.

(* Bezout_coprimepP skipped *)

lemma coprimep_root p q x :
  coprimep p q => root p x => peval q x <> IDCoeff.zeror.
proof.
admitted.

lemma Gauss_dvdpl p q d: coprimep d q => dvdp d (p * q) = dvdp d p.
proof.
admitted.

lemma Gauss_dvdpr p q d: coprimep d q => dvdp d (q * p) = dvdp d p.
proof.
admitted.

lemma Gauss_dvdp m n p : coprimep m n => dvdp (m * n) p = dvdp m p && dvdp n p.
proof.
admitted.

lemma Gauss_gcdpr p m n : coprimep p m => eqp (gcdp p (m * n)) (gcdp p n).
proof.
admitted.

lemma Gauss_gcdpl p m n : coprimep p n => eqp (gcdp p (m * n)) (gcdp p m).
proof.
admitted.

lemma coprimepMr (p q r : poly) :
  coprimep p (q * r) = (coprimep p q && coprimep p r).
proof.
admitted.

lemma coprimepMl (p q r : poly) :
  coprimep (q * r) p = (coprimep q p && coprimep r p).
proof.
admitted.

lemma modp_coprime k u n :
  k <> poly0 => eqp (modp (k * u) n) poly1 => coprimep k n.
proof.
admitted.

lemma coprimep_pexpl k m n :
  0 < k => coprimep (PolyComRing.exp m k) n = coprimep m n.
proof.
admitted.

lemma coprimep_pexpr k m n :
  0 < k => coprimep m (PolyComRing.exp n k) = coprimep m n.
proof.
admitted.

lemma coprimep_expl k m n : coprimep m n => coprimep (PolyComRing.exp m k) n.
proof.
admitted.

lemma coprimep_expr k m n : coprimep m n => coprimep m (PolyComRing.exp n k).
proof.
admitted.

lemma gcdp_mul2l (p q r : poly) : eqp (gcdp (p * q) (p * r)) (p * gcdp q r).
proof.
admitted.

lemma gcdp_mul2r (q r p : poly) : eqp (gcdp (q * p) (r * p)) (gcdp q r * p).
proof.
admitted.

lemma mulp_gcdr p q r : eqp (r * (gcdp p q)) (gcdp (r * p) (r * q)).
proof.
admitted.

lemma mulp_gcdl p q r : eqp ((gcdp p q) * r) (gcdp (p * r) (q * r)).
proof.
admitted.

lemma coprimep_div_gcd p q :
  (p <> poly0) || (q <> poly0) =>
  coprimep (divp p (gcdp p q)) (divp q (gcdp p q)).
proof.
admitted.

lemma divp_eq0 p q :
  (divp p q = poly0) = (p = poly0 || q = poly0 || deg p < deg q).
proof.
admitted.

lemma dvdp_div_eq0 p q : dvdp q p => (divp p q = poly0) = (p = poly0).
proof.
admitted.

(* Bezout_coprimepPn skipped *)

lemma dvdp_pexp2r m n k :
  0 < k => dvdp (PolyComRing.exp m k) (PolyComRing.exp n k) = dvdp m n.
proof.
admitted.

lemma root_gcd p q x : root (gcdp p q) x = root p x && root q x.
proof.
admitted.

lemma root_biggcd x ps :
  root (foldr gcdp poly0 ps) x = all (fun p => root p x) ps.
proof.
elim ps; 2: by smt(root_gcd).
by smt(IDCoeff.addr0 IDCoeff.mul0r deg0 poly0E rangeS).
qed.

(* It will go through useless loops once "coprimep p q"
   since iter is needed as recursive calls are currently not allowed. *)
op gdcop_rec_it (i : poly * poly) =
  let (q, p) = i in
  if coprimep p q then i else (q, divp p (gcdp p q)).

op gdcop_rec (q p : poly) (k : int) =
  let (pp, qq) = iter k gdcop_rec_it (q, p) in
  if coprimep pp qq then pp else IDD.ComRing.RPD.eqpoly0p qq.

op gdcop (q p : poly) =
  let (pp, qq) = iter (deg p) gdcop_rec_it (q, p) in
  if coprimep pp qq then pp else IDD.ComRing.RPD.eqpoly0p qq.

op gdcop_spec (q p r : poly) =
  dvdp r p && (coprimep r q || p = poly0) &&
  (forall d, dvdp d p => coprimep d q => dvdp d r).

lemma gdcop0 q : gdcop q poly0 = IDD.ComRing.RPD.eqpoly0p q.
proof.
admitted.

lemma gdcop_recP q p k : deg p <= k => gdcop_spec q p (gdcop_rec q p k).
proof.
admitted.

lemma gdcopP q p : gdcop_spec q p (gdcop q p).
proof.
admitted.

lemma coprimep_gdco p q : q <> poly0 => coprimep (gdcop p q) p.
proof.
admitted.

lemma size2_dvdp_gdco p q d :
  p <> poly0 => deg d = 2 =>
  (dvdp d (gdcop q p)) = (dvdp d p) && ! (dvdp d q).
proof.
admitted.

lemma dvdp_gdco p q : dvdp (gdcop p q) q.
proof.
admitted.

lemma root_gdco p q x :
  p <> poly0 => root (gdcop q p) x = root p x && ! root q x.
proof.
admitted.

op comp_poly (p q : poly) =
  BigPoly.PCM.bigi predT (fun i => p.[i] ** PolyComRing.exp q i) 0 (deg p).

lemma dvdp_comp_poly r p q : dvdp p q => dvdp (comp_poly p r) (comp_poly q r).
proof.
admitted.

lemma gcdp_comp_poly r p q :
  eqp (gcdp p (comp_poly q r)) (gcdp (comp_poly p r) (comp_poly q r)).
proof.
admitted.

lemma coprimep_comp_poly r p q :
  coprimep p q => coprimep (comp_poly p r) (comp_poly q r).
proof.
admitted.

lemma coprimep_addl_mul (p q r : poly) : coprimep r (p * r + q) = coprimep r q.
proof.
admitted.

op irreducible_poly p =
  (1 < deg p) && (forall q, deg q <> 1 => dvdp q p => eqp q p).

end CommonIdomain.
