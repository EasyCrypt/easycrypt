require import AllCore List IntDiv StdOrder.
import IntOrder.

(* -------------------------------------------------------------------- *)
(* Pocklington's criterion (after coqprime, PrimalityTest/Pocklington.v) *)

(* F divides m as soon as, for each prime p dividing F, some divisor o  *)
(* of both m and D leaves a cofactor D %/ o that p does not divide.     *)
lemma pocklington_dvd (F D m : int) : 0 < D => F %| D =>
  (forall p, prime p => p %| F =>
     exists o, o %| m /\ o %| D /\ ! p %| (D %/ o)) =>
  F %| m.
proof.
move=> gt0_D dvd_FD hp; pose L := gcd D m.
have nz_L : L <> 0 by rewrite /L gcd_eq0 /#.
have dvd_LD : L %| D by apply: dvdz_gcdl.
have nz_F : F <> 0 by apply: contraL dvd_FD => ->; rewrite dvd0z /#.
have cop : coprime F (D %/ L).
- rewrite /coprime; pose g := gcd F (D %/ L).
  have ge0_g : 0 <= g by apply: ge0_gcd.
  have nz_g : g <> 0 by rewrite /g gcd_eq0 /#.
  case: (g = 1) => // ne1_g; case: (pdivP g _); 1: smt().
  move=> p [pr_p dvd_pg].
  have dvd_pF : p %| F by apply: (dvdz_trans g) => //; apply: dvdz_gcdl.
  have dvd_pDL : p %| D %/ L by apply: (dvdz_trans g) => //; apply: dvdz_gcdr.
  case: (hp p pr_p dvd_pF) => o [dvd_om [dvd_oD ndvd]].
  have dvd_oL : o %| L by apply: dvdz_gcd.
  have nz_o : o <> 0 by apply: contraL dvd_oD => ->; rewrite dvd0z /#.
  have hDo : D %/ o = D %/ L * (L %/ o).
  - have hD : D = D %/ L * (L %/ o) * o by rewrite -mulrA !divzK.
    by rewrite {1}hD mulzK.
  have : p %| D %/ o by rewrite hDo; apply: dvdz_mulr.
  by move=> h; have := ndvd; rewrite h.
have dvd_FL : F %| L.
- by apply: (Gauss _ (D %/ L)) => //; rewrite divzK.
by apply: (dvdz_trans L) => //; apply: dvdz_gcdr.
qed.

lemma pocklington_mulorder (N q p a : int) : 1 < N => prime q => q %| N =>
  prime p => p %| (N - 1) =>
  a ^ (N - 1) %% N = 1 => coprime (a ^ ((N - 1) %/ p) - 1) N =>
     mulorder a q %| (q - 1)
  /\ mulorder a q %| (N - 1)
  /\ ! p %| ((N - 1) %/ mulorder a q).
proof.
move=> gt1_N pr_q dvd_qN pr_p dvd_pD haN cop.
have gt1_q := gt1_prime q pr_q; have gt1_p := gt1_prime p pr_p.
have haq : a ^ (N - 1) %% q = 1.
- by rewrite -(modz_dvd _ N q) // haN modz_small /#.
have ndvd_qa : ! q %| a.
- apply/negP => dvd_qa; move: haq; rewrite (_ : N - 1 = (N - 2) + 1) 1:/#.
  rewrite exprS 1:/#; have := dvdz_mulr q a (a ^ (N - 2)) dvd_qa.
  by rewrite dvdzE => ->.
have dvd_oD : mulorder a q %| (N - 1) by rewrite (mulorder_dvdz a q (N - 1)) 1,3:/#.
do! split => //; first by apply: mulorder_dvd_pred.
apply/negP => dvd_p; pose o := mulorder a q; have gt0_o : 0 < o.
- by apply: (mulorder_gt0 a q (N - 1)) => /#.
case/dvdzP: dvd_p => t ht.
have hD : N - 1 = t * o * p by rewrite -(divzK o (N - 1)) // ht; ring.
have dvd_oDp : o %| ((N - 1) %/ p).
- by rewrite hD mulzK 1:/#; apply: dvdz_mull; apply: dvdzz.
have : a ^ ((N - 1) %/ p) %% q = 1.
- have gt0_D : 0 < N - 1 by smt().
  have ge0_Dp : 0 <= (N - 1) %/ p by rewrite divz_ge0 /#.
  by rewrite -(mulorder_dvdz a q (N - 1) _ gt0_D haq ge0_Dp).
move=> h1; have dvd_q1 : q %| (a ^ ((N - 1) %/ p) - 1).
- by rewrite eqz_mod_dvd h1 modz_small /#.
have := dvdz_gcd q _ _ dvd_q1 dvd_qN; move: cop; rewrite /coprime => ->.
by rewrite dvdz1; smt().
qed.

lemma pocklington (N F1 R1 : int) : 1 < F1 => 0 < R1 => N - 1 = F1 * R1 =>
  (forall p, prime p => p %| F1 =>
     exists a, a ^ (N - 1) %% N = 1 /\ coprime (a ^ ((N - 1) %/ p) - 1) N) =>
  forall q, prime q => q %| N => q %% F1 = 1.
proof.
move=> gt1_F gt0_R hN hp q pr_q dvd_qN.
have le_F : F1 <= F1 * R1 by apply: ler_pemulr => /#.
have gt1_N : 1 < N by smt().
have dvd_F : F1 %| (q - 1).
- apply: (pocklington_dvd F1 (N - 1)); 1: smt().
  + by rewrite hN; apply: dvdz_mulr; apply: dvdzz.
  move=> p pr_p dvd_pF; case: (hp p pr_p dvd_pF) => a [haN cop].
  have dvd_pD : p %| (N - 1) by rewrite hN; apply: dvdz_mulr.
  have [#] := pocklington_mulorder N q p a gt1_N pr_q dvd_qN pr_p dvd_pD haN cop.
  by move=> h1 h2 h3; exists (mulorder a q).
by rewrite (_ : q = (q - 1) + 1) 1:/# dvdz_modzDl // modz_small /#.
qed.

lemma pocklington_prime (N F1 R1 : int) :
  1 < F1 => 0 < R1 => N - 1 = F1 * R1 => N < F1 * F1 =>
  (forall p, prime p => p %| F1 =>
     exists a, a ^ (N - 1) %% N = 1 /\ coprime (a ^ ((N - 1) %/ p) - 1) N) =>
  prime N.
proof.
move=> gt1_F gt0_R hN lt_N hp; apply: contraT => npr_N.
have gt1_N : 1 < N by smt().
move: npr_N; rewrite primePns => -[/#|[q [pr_q [le_q2 dvd_qN]]]].
have hq := pocklington N F1 R1 gt1_F gt0_R hN hp q pr_q dvd_qN.
have gt1_q := gt1_prime q pr_q.
have lt_Fq : F1 < q.
- have := divz_eq q F1; rewrite hq; pose k := q %/ F1; move=> eq_q.
  have ge0_k : 0 <= k by rewrite /k divz_ge0 /#.
  have : F1 <= k * F1 by case: (k = 0) => [/#|nz_k]; apply: ler_pemull => /#.
  smt().
have := ltr_pmul F1 q F1 q _ _ lt_Fq lt_Fq; 1,2: smt().
by move: le_q2; rewrite expr2; smt().
qed.

(* -------------------------------------------------------------------- *)
(* A certificate for N is a list of pairs (p, a): F1 is the product of  *)
(* the p's (with multiplicity), and a is the witness for p.             *)
op pock_F1 (c : (int * int) list) =
  foldr (fun (pa : int * int) f => pa.`1 * f) 1 c.

op pock_check (N : int) (c : (int * int) list) =
  let F1 = pock_F1 c in
     1 < N /\ 1 < F1 /\ (N - 1) %% F1 = 0 /\ N < F1 * F1
  /\ all (fun (pa : int * int) =>
           powmod pa.`2 N (N - 1) = 1
        /\ gcd ((powmod pa.`2 N ((N - 1) %/ pa.`1) - 1) %% N) N = 1) c.

lemma pock_F1P (p : int) (c : (int * int) list) : prime p =>
  p %| pock_F1 c => exists pa, pa \in c /\ p %| pa.`1.
proof.
move=> pr_p; elim: c => [|pa c ih] /=.
- by rewrite /pock_F1 /= dvdzE modz_small; smt(gt1_prime).
rewrite /pock_F1 /= -/(pock_F1 c) => /Euclide /(_ pr_p).
case=> [h|/ih [qa [qa_in h]]]; first by exists pa.
by exists qa; rewrite /= qa_in h.
qed.

lemma pock_certif (N : int) (c : (int * int) list) :
  pock_check N c => all (fun (pa : int * int) => prime pa.`1) c => prime N.
proof.
rewrite /pock_check /=; pose F1 := pock_F1 c.
move=> [#] gt1_N gt1_F dvd_F lt_N /allP hc /allP pr_c.
have eq_N : N - 1 = F1 * ((N - 1) %/ F1).
- by rewrite mulrC divzK // dvdzE.
apply: (pocklington_prime N F1 ((N - 1) %/ F1)) => //.
- by rewrite ltz_divRL // ?dvdzE /#.
move=> p pr_p /(pock_F1P p c pr_p) [[q a] [qa_in dvd_pq]].
have pr_q := pr_c _ qa_in; have [#] := hc _ qa_in => /=.
rewrite /powmod => h1 h2; exists a; split => //.
have -> : p = q.
- case: pr_q => _ /(_ p dvd_pq); smt(gt1_prime).
by move: h2; rewrite modzDml -coprime_modl /coprime.
qed.
