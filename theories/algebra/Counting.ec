(* ==================================================================== *)
require import AllCore Ring List Int IntMin IntDiv Bigalg Binomial Finite Poly StdBigop.
(*---*) import StdOrder.IntOrder IntID Bigint.


(* ==================================================================== *)
(*TODO: can I use this with elim, and how?*)
(*
inductive prime_spec n =
  | Le1 of (n <= 1)
  | Prime of (prime n)
  | Composite a b of (1 < a) & (1 < b) & (n = a * b).

lemma primeW n :
  prime_spec n.
proof.
case (n <= 1) => [len1|/ltrNge lt1n]; [by apply/Le1|].
case (prime n) => [prime_n|]; [by apply/Prime|].
rewrite /prime lt1n /= negb_forall /=; case => a.
rewrite negb_imply negb_or => -[dvdan] [neq_1 neq_n].
apply/(Composite n `|a| (n %/ `|a|)).
+ rewrite ltrNge; apply/negP => le_1; move: (le2_mem_range 0 1 `|a|).
  rewrite normr_ge0 le_1 /= 2?range_ltn //= range_geq //= neq_1 /=.
  by apply/gtr_eqF/normr_gt0/negP => ->>; move/dvd0z: dvdan => ->>.
+ rewrite ltz_divRL /=; [|by apply/dvdz_norml|].
  - by apply/normr_gt0/negP => ->>; move/dvd0z: dvdan => ->>.
  move: (dvdz_le _ _ _ dvdan); [by apply/gtr_eqF/ltzE/ltzW|].
  by rewrite (gtr0_norm n) 1:ltzE 1:ltzW // => /ler_eqVlt [|//]; rewrite neq_n.
by rewrite mulrC divzK // dvdz_norml.
qed.
*)


(* ==================================================================== *)
(*TODO: surely some of this is done elsewhere, and move where appropriate.*)
lemma le_ind P (m : int) :
  P m =>
  (forall n , m <= n => P n => P (n + 1)) =>
  (forall n , m <= n => P n).
proof.
  move => Pm IH n /subr_ge0 le0_; rewrite -(subrK n m).
  elim: (n - m) le0_ => {n} [|n le0n IHn] //.
  by rewrite addrAC; apply/IH => //; apply/ler_addr.
qed.

lemma lt_ind P (m : int) :
  P (m + 1) =>
  (forall n , m < n => P n => P (n + 1)) =>
  (forall n , m < n => P n).
proof. by move => P_ IH n /ltzE; apply/le_ind => // {n} n /ltzE; apply/IH. qed.

lemma strong_ind P :
  P 0 =>
  (forall n , 0 <= n => (forall k , k \in range 0 n => P k) => P n) =>
  (forall n , 0 <= n => P n).
proof.
  move => P0 IHS n le0n; elim: n le0n {1 2 4}n (le0n) (lerr n) => [|n le0n IHn] k.
  + by move => le0k lek0; move: (eqz_leq k 0); rewrite lek0 le0k /= => ->>.
  move => le0k /ler_eqVlt [->> {le0k}|/ltzS]; [|by apply/IHn].
  by apply/IHS; [apply/addr_ge0|move => k /mem_range [le0k /ltzS lekn]; apply/IHn].
qed.

lemma le_strong_ind P (m : int) :
  P m =>
  (forall n , m <= n => (forall k , k \in range m n => P k) => P n) =>
  (forall n , m <= n => P n).
proof.
  move => Pm IH n /subr_ge0 le0_; rewrite -(subrK n m); move: (n - m) le0_ => +.
  move => {n} n le0n; pose Q n:= P (n + m); apply/(strong_ind Q) => //.
  move => {n le0n} n le0n IHn; rewrite /(Q _); apply/IH; [by apply/ler_addr|].
  by move => k mem_; rewrite -(subrK k m); apply/IHn/mem_range_subr.
qed.

lemma lt_strong_ind P (m : int) :
  P (m + 1) =>
  (forall n , m < n => (forall k , k \in range (m + 1) n => P k) => P n) =>
  (forall n , m < n => P n).
proof. by move => P_ IH n /ltzE; apply/le_strong_ind => // ? /ltzE; apply/IH. qed.

lemma add_ind P :
  P 1 =>
  (forall m n , 0 < m => 0 < n => P m => P n => P (m + n)) =>
  (forall n , 0 < n => P n).
proof. by move => P1 IHA; apply/lt_ind => // n lt0n Pn; apply/IHA. qed.

lemma mul_ind P :
  (forall p , prime p => P p) =>
  (forall m n , 1 < m => 1 < n => P m => P n => P (m * n)) =>
  (forall n , 1 < n => P n).
proof.
  move => Pp IHM; apply/lt_strong_ind => /=; [by apply/Pp/prime2|].
  move => n lt1n IHn; case: (prime n) => [prime_n|Nprime_n]; [by apply/Pp|].
  case: (compositeP _ lt1n Nprime_n) => a b [lt1a] [lt1b] ->>; apply/IHM => //.
  + apply/IHn/mem_range; rewrite -ltzS -ltr_subl_addr lt1a /=; apply/subr_gt0.
    by rewrite -mulN1r mulrC -mulrDl; apply/mulr_gt0; [apply/subr_gt0|apply/ltzE/ltzW].
  apply/IHn/mem_range; rewrite -ltzS -ltr_subl_addr lt1b /=; apply/subr_gt0.
  by rewrite -mulN1r -mulrDl; apply/mulr_gt0; [apply/subr_gt0|apply/ltzE/ltzW].
qed.

lemma coprime_ind P :
  (forall p n , prime p => 0 < n => P (p ^ n)) =>
  (forall m n , 1 < m => 1 < n => coprime m n => P m => P n => P (m * n)) =>
  (forall n , 1 < n => P n).
proof.
  move => Ppp IHM; apply/lt_strong_ind => /=; [by move: (Ppp _ 1 prime2 _); rewrite // expr1|].
  move => n lt1n IHn; case: (pow_prime_divisors n _); [by apply/ltzE/ltzW|].
  case => [/is_ppdec_nil ->> //|[p k] pps /is_ppdec_cons |> [prime_p _] lt0k dvd_ Ndvd_ _].
  case (n = p ^ k) => [->>|neq]; [by apply/Ppp|]; rewrite -(divzK _ _ dvd_); apply/IHM.
  + apply/ltz_divRL => //=; [by apply/expr_gt0/gt0_prime|].
    move: (dvdz_le _ _ _ dvd_); [by apply/gtr_eqF/ltzE/ltzW|].
    rewrite gtr0_norm; [by apply/expr_gt0/gt0_prime|]; rewrite gtr0_norm; [by apply/ltzE/ltzW|].
    by move => /ler_eqVlt; rewrite eq_sym neq.
  + apply/(ltr_le_trans p); [by apply/gt1_prime|]; rewrite -{1}expr1.
    by apply/ler_weexpn2l => /=; [apply/ltzW/gt1_prime|move/ltzE: lt0k].
  + by apply/coprimeC/coprime_pow_prime => //; rewrite prime_gcd.
  + apply/IHn/mem_range; rewrite ltz_divLR; [by apply/expr_gt0/gt0_prime|].
    rewrite -subr_gt0 -mulN1r mulrC -mulrDl mulr_gt0 /=; [|by apply/ltzE/ltzW| ].
    - apply/subr_gt0/(ltr_le_trans p); [by apply/gt1_prime|]; rewrite -{1}expr1.
      by apply/ler_weexpn2l => /=; [apply/ltzW/gt1_prime|move/ltzE: lt0k].
    apply/ltzS/ltr_subl_addr/ltz_divRL => //=; [by apply/expr_gt0/gt0_prime|].
    move: (dvdz_le _ _ _ dvd_); [by apply/gtr_eqF/ltzE/ltzW|].
    rewrite gtr0_norm; [by apply/expr_gt0/gt0_prime|]; rewrite gtr0_norm; [by apply/ltzE/ltzW|].
    by move => /ler_eqVlt; rewrite eq_sym neq.
  apply/IHn/mem_range; move: (dvdz_le _ _ _ dvd_); [by apply/gtr_eqF/ltzE/ltzW|].
  rewrite gtr0_norm; [by apply/expr_gt0/gt0_prime|]; rewrite gtr0_norm; [by apply/ltzE/ltzW|].
  move => /ler_eqVlt; rewrite eq_sym neq /= => -> /=; apply/ltzS/ltr_subl_addr => /=.
  apply/(ltr_le_trans p); [by apply/gt1_prime|]; rewrite -{1}expr1.
  by apply/ler_weexpn2l => /=; [apply/ltzW/gt1_prime|move/ltzE: lt0k].
qed.


(* ==================================================================== *)
op coprimes n = filter (coprime n) (range 1 (n + 1)).

lemma coprimesP n k :
  k \in coprimes n <=> (coprime n k /\ k \in range 1 (n + 1)).
proof. by rewrite mem_filter. qed.

lemma coprimes_uniq n :
  uniq (coprimes n).
proof. by apply/filter_uniq/range_uniq. qed.

lemma coprimes_sorted n :
  sorted Int.(<=) (coprimes n).
proof. by apply/sorted_filter; [apply/ler_trans|apply/sorted_range]. qed.

lemma coprimes_nil n :
  n <= 0 =>
  coprimes n = [].
proof. by move => ?; rewrite /coprimes range_geq // -ler_subr_addr. qed.

lemma coprimes1 :
  coprimes 1 = [1].
proof. by rewrite /coprimes range_ltn // range_geq. qed.

lemma coprimes_mem1 n :
  1 <= n <=> 1 \in coprimes n.
proof. by rewrite coprimesP /coprime gcdz1 /= mem_range ltzS. qed.

lemma coprimes_subseq n :
  1 < n =>
  subseq (coprimes n) (range 1 n).
proof.
  move => lt1n; rewrite /coprimes rangeSr ?ltzW //.
  rewrite filter_rcons /coprime gcdzz eqr_norml /=.
  case (n = -1) => [->>|_] //=; case (n = 1) => [->>|_] //=.
  by apply/filter_subseq.
qed.

lemma coprimes_incl n :
  1 < n =>
  mem (coprimes n) <= mem (range 1 n).
proof. by move/coprimes_subseq/subseq_mem. qed.

lemma coprimes_prime p :
  prime p =>
  coprimes p = range 1 p.
proof.
  move => /primeP [lt1p mem_]; rewrite /coprimes rangeSr ?ltzW //.
  rewrite filter_rcons eq_in_filter_predT // /coprime gcdzz.
  by rewrite gtr_eqF // ltr_normr lt1p.
qed.

lemma coprimes_pow_prime p n :
  prime p =>
  0 < n =>
  coprimes (p ^ (n + 1)) =
  flatten (mkseq (fun k => map (Int.(+) (k * p ^ n)) (coprimes (p ^ n))) p).
proof.
  move => prime_p lt0n; move/ltzW: (lt0n) => le0n; apply/(eq_sorted Int.(<=)) => //.
  + by apply/ler_trans.
  + by move => ? ? ? ?; apply/ler_anti; split.
  + by apply/coprimes_sorted.
  + apply/(sorted_flatten _ _ ler_trans); split.
    - apply/allP => ? /mapP [x] [+ ->>]; rewrite range_iota /= => mem_.
      apply/sorted_map; [|by apply/coprimes_sorted].
      by move => ? ? ?; apply/ler_add2l.
    rewrite eq_in_filter_predT.
    - move => ? /mapP [?] [? eq_]; rewrite /predC1; apply/negP => ->>.
      move/(congr1 size): eq_ => /=; rewrite size_map; apply/negP.
      move => /eq_sym /size_eq0 eq_; move: (coprimes_mem1 (p ^ n)).
      by rewrite eq_ /=; apply/ltzS/ltr_subl_addr/expr_gt0/gt0_prime.
    rewrite /mkseq range_iota /= -(subrr p); move/ltzW: (gt0_prime _ prime_p).
    elim: {1 5} p => [|k le0k IHk]; [by rewrite range_geq|].
    rewrite range_ltn; [by apply/ltr_subl_addr/ltr_subl_addl/ltzS|].
    rewrite map_cons sorted_cons; [|rewrite opprD !addrA /= IHk /=].
    - move => [|x2 s2] s1 s3 |> neq1 le12 neq3 le23 x1 x3 mem1 mem3.
      by apply/(ler_trans x2); [apply/le12|apply/le23].
    move => {IHk} ? /mapP [i] [mem_ ->>]; split; [|split].
    - rewrite -size_eq0 size_map size_eq0; apply/negP => eq_; move: (coprimes_mem1 (p ^ n)).
      by rewrite eq_ /=; apply/ltzS/ltr_subl_addr/expr_gt0/gt0_prime.
    - rewrite -size_eq0 size_map size_eq0; apply/negP => eq_; move: (coprimes_mem1 (p ^ n)).
      by rewrite eq_ /=; apply/ltzS/ltr_subl_addr/expr_gt0/gt0_prime.
    move => ? ? /mapP [x1] [/coprimesP [_ mem1] ->>] /mapP [x2] [/coprimesP [_ mem2] ->>].
    apply/(ler_trans ((p - k) * p ^ n)).
    - apply/ler_subr_addl; rewrite -mulNr -mulrDl opprD addrA /=.
      by move: mem1; apply/mem_range_ge.
    apply/(ler_trans (i * p ^ n)).
    - by apply/ler_pmul2r; [apply/expr_gt0/gt0_prime|move: mem_; apply/mem_range_le].
    by apply/ler_subl_addl => /=; move: mem2; apply/mem_range_le.
  apply/uniq_perm_eq.
  + by apply/coprimes_uniq.
  + apply/uniq_flatten_map => //=.
    - by move => ?; apply/uniq_map_injective; [apply/addrI|apply/coprimes_uniq].
    - rewrite range_iota /=; move => x y memx memy /hasP [?] [].
      move => /mapP [z] [/coprimesP [_ memz] ->>] /mapP [t] [/coprimesP [_ memt] eq_].
      move/(congr1 (transpose Int.(-) 1)): eq_ => /=; rewrite -!addrA.
      move: (mem_range_addr 0 (p ^ n) z (-1)) (mem_range_addr 0 (p ^ n) t (-1)) memz memt.
      move => <- <-; move: (z - 1) (t - 1) => {z t} z t memz memt eq_.
      move: (euclideU _ _ _ _ _ eq_); rewrite -!mem_range gtr0_norm ?expr_gt0 ?gt0_prime //.
      by rewrite memz memt /= => [].
    by rewrite range_iota; apply/range_uniq.
  move => x; rewrite coprimesP -flatten_mapP range_iota /=; split.
  + move => [cpx]; rewrite rangeSr; [by apply/ltzS/ltr_subl_addr/expr_gt0/gt0_prime|].
    rewrite mem_rcons /=; case => [->>|memx].
    - move: cpx; rewrite /coprime gcdzz gtr_eqF // ltr_normr; left.
      apply/(ltr_le_trans p); [by apply/gt1_prime|rewrite -{1}expr1].
      by apply/ler_weexpn2l; [apply/ltzW/gt1_prime|rewrite /= -ler_subl_addr].
    exists (x %/ (p ^ n)); split.
    - apply/range_div_range; [by apply/expr_gt0/gt0_prime|].
      by rewrite /= -exprS //; move: memx; apply/mem_range_incl.
    apply/mapP; exists (x %% (p ^ n)); rewrite -divz_eq /=.
    apply/coprimesP; split.
    - move: cpx; rewrite /coprime gcd_modr => eq_.
      move: (dvdz_gcd2 (p ^ n) (p ^ (n + 1)) x _).
      * by apply/le_dvd_pow; rewrite ger0_norm // gtr0_norm ?ltzS //; apply/ltzW/ltzS.
      by move: eq_ => -> /dvdz1; rewrite ger0_norm // ge0_gcd.
    move: (mem_range_mod x (p ^ n)); rewrite gtr_eqF /=; [by apply/expr_gt0/gt0_prime|].
    rewrite gtr0_norm; [by apply/expr_gt0/gt0_prime|].
    rewrite range_ltn /=; [by apply/expr_gt0/gt0_prime|].
    case; [|by apply/mem_range_incl => //; apply/ltzW/ltzS].
    rewrite -dvdzE => dvd_; move: (dvdz_gcd (p ^ (n + 1)) x (p ^ n)).
    rewrite le_dvd_pow /=; [by rewrite ger0_norm // gtr0_norm ?ltzS //; apply/ltzW/ltzS|].
    move: cpx => ->; rewrite dvdz1 gtr0_norm; [by apply/expr_gt0/gt0_prime|].
    move => eq_; move: eq_ dvd_ => <-; rewrite ieexprn_weq1 // ?ltzW ?gt0_prime //.
    by case => [->> //|_ ->>]; move/gt1_prime: prime_p.
  move => [y] [mem_ /mapP [z] [/coprimesP [cpz mem_z] ->>]]; split.
  + by move: cpz; rewrite -(coprimeMDl y) !coprime_pow_prime //; apply/ltzS.
  move: mem_z; rewrite -{1 3}(add0r 1) -!mem_range_subr -!addrA => mem_z.
  move: (mem_range_add_mul _ _ _ _ _ mem_z mem_); rewrite /= -exprS //.
  by rewrite (addrC (_ - 1)) (mulrC _ y).
qed.

lemma coprimes_coprime m n :
  1 < m =>
  1 < n =>
  coprime m n =>
  perm_eq (map (fun k => (k %% m, k %% n)) (coprimes (m * n))) (allpairs (fun a b => (a, b)) (coprimes m) (coprimes n)).
proof.
  move => lt1m lt1n copmn; apply/uniq_perm_eq.
  + rewrite map_inj_in_uniq; [|by apply/coprimes_uniq].
    move => x y; move: (coprimes_subseq (m * n)).
    rewrite mulr_egt1 //= => subseq_ memx memy.
    move: (subseq_mem _ _ _ subseq_ memx) (subseq_mem _ _ _ subseq_ memy).
    move => {memx memy} memx memy [].
    case: (Bezout _ _ copmn) => u v eq1 eqm eqn.
    rewrite -(modz_small x (m * n)).
    - apply/mem_range; rewrite normrM gtr0_norm ?ltzE ?ltzW //.
      by rewrite gtr0_norm ?ltzE ?ltzW //; move: memx; apply/mem_range_incl.
    rewrite -(modz_small y (m * n)).
    - apply/mem_range; rewrite normrM gtr0_norm ?ltzE ?ltzW //.
      by rewrite gtr0_norm ?ltzE ?ltzW //; move: memy; apply/mem_range_incl.
    by rewrite chinese_remainder_theorem_unicity.
  + apply/allpairs_uniq; [by apply/coprimes_uniq|by apply/coprimes_uniq|].
    by move => ? ? ? ?.
  move => [x y]; rewrite mapP allpairsP; split => [[z] /= [mem_ [->> ->>]]|].
  + exists (z %% m, z %% n) => /=; move: mem_; rewrite !coprimesP.
    move => [cop_ mem_]; move: (mem_range_mod z m) (mem_range_mod z n).
    rewrite gtr_eqF ?ltzE ?ltzW // gtr_eqF ?ltzE ?ltzW //=.
    rewrite gtr0_norm ?ltzE ?ltzW // gtr0_norm ?ltzE ?ltzW //.
    rewrite (range_ltn _ m) ?ltzE ?ltzW // (range_ltn _ n) ?ltzE ?ltzW //=.
    rewrite -!dvdzE; case => [dvdm|memm].
    - move: (dvdz_gcd (m * n) z m); rewrite dvdz_mulr ?dvdzz //= => eq_; move: eq_ dvdm => <-.
      by rewrite cop_ => /dvdz1; rewrite gtr0_norm ?ltzE ?ltzW // => ->>.
    case => [dvdn|memn].
    - move: (dvdz_gcd (m * n) z n); rewrite dvdz_mull ?dvdzz //= => eq_; move: eq_ dvdn => <-.
      by rewrite cop_ => /dvdz1; rewrite gtr0_norm ?ltzE ?ltzW // => ->>.
    move: cop_; rewrite /coprime !gcd_modr => eq1.
    move: (dvdz_gcd2 m (m * n) z); rewrite dvdz_mulr ?dvdzz // eq1 /=.
    move => /dvdz1; rewrite ger0_norm ?ge0_gcd // => -> /=.
    move: (dvdz_gcd2 n (m * n) z); rewrite dvdz_mull ?dvdzz // eq1 /=.
    move => /dvdz1; rewrite ger0_norm ?ge0_gcd // => -> /=.
    by split; [move: memm|move: memn]; apply/mem_range_incl => //; apply/ltzW/ltzS.
  move => [] [? ?] /= [memx] [memy] [<<- <<-].
  case: (chinese_remainder_theorem_exists _ _ copmn x y) => z [eqm eqn].
  exists (z %% (m * n)); rewrite !modz_dvd; [by apply/dvdz_mulr/dvdzz|by apply/dvdz_mull/dvdzz|].
  rewrite eqm eqn (modz_small x) ?(modz_small y) -?mem_range ?gtr0_norm ?ltzE ?ltzW //=.
  + by move/(coprimes_incl _ lt1m): memx; apply/mem_range_incl.
  + by move/(coprimes_incl _ lt1n): memy; apply/mem_range_incl.
  apply/coprimesP; rewrite coprime_modr coprimeMl_and.
  rewrite -coprime_modr eqm coprime_modr; move: memx => /coprimesP => -[copx _]; rewrite copx /=.
  rewrite -coprime_modr eqn coprime_modr; move: memy => /coprimesP => -[copy _]; rewrite copy /=.
  move: (mem_range_mod z (m * n)); rewrite normrM mulf_neq0 /=.
  + by apply/gtr_eqF/ltzE/ltzW.
  + by apply/gtr_eqF/ltzE/ltzW.
  rewrite !gtr0_norm ?ltzE ?ltzW // range_ltn /=.
  + by apply/mulr_gt0; apply/ltzE/ltzW.
  case; [|by apply/mem_range_incl => //; apply/ltzW/ltzS].
  rewrite -dvdzE => /mulz_dvdl dvd_; move: copx.
  rewrite -coprime_modr -eqm coprime_modr => /(dvdr_coprime _ _ _ dvd_).
  by rewrite coprimezz gtr_eqF // ltr_normr lt1m.
qed.

(* ------------------------------------------------------------------- *)
op phi n = size (coprimes n).

lemma phi_ge0 n :
  0 <= phi n.
proof. by apply/size_ge0. qed.

lemma phi_eq0 n :
  n <= 0 =>
  phi n = 0.
proof. by move => len0; rewrite /phi coprimes_nil. qed.

lemma phi1 :
  phi 1 = 1.
proof. by rewrite /phi coprimes1. qed.

lemma phi_gt0 n :
  1 <= n =>
  0 < phi n.
proof. by rewrite /phi -has_predT hasP => /coprimes_mem1 ?; exists 1; rewrite /predT. qed.

lemma phi_ltid n :
  1 < n =>
  phi n < n.
proof.
move => lt1n; move/coprimes_subseq/subseq_size: (lt1n); rewrite /phi size_range.
by move => le_; apply/(ler_lt_trans _ _ _ le_)/ltr_maxrP; rewrite ltzE ltzW //= ltzE.
qed.

lemma phi_prime p :
  prime p =>
  phi p = p - 1.
proof.
rewrite /phi => prime_p; move/coprimes_prime: (prime_p) => ->.
by rewrite size_range maxrE subr_le0 lerNgt gt1_prime.
qed.

lemma phi_pow_prime p n :
  prime p =>
  0 < n =>
  phi (p ^ n) = p ^ n - p ^ (n - 1).
proof.
  move => prime_p; rewrite /phi -{1 2 3}(subrK n 1); move: (n - 1) => {n} n /ltzS.
  elim: n => [|n le0n IHn].
  + by rewrite expr1 expr0 coprimes_prime // size_range ler_maxr // -ltzS; apply/gt0_prime.
  rewrite coprimes_pow_prime ?ltzS //= size_flatten sumzE !BIA.big_mapT.
  rewrite (BIA.eq_big _ predT _ (fun _ => p ^ (n + 1) - p ^ n)) //.
  + by move => i _; rewrite /(\o) /= size_map.
  rewrite big_constz count_predT size_iota ler_maxr ?ltzW ?gt0_prime //.
  by rewrite mulrDl mulNr -!exprSr // addr_ge0.
qed.

lemma phi_coprime m n :
  0 < m =>
  0 < n =>
  coprime m n =>
  phi (m * n) = phi m * phi n.
proof.
  move => /ltzE /ler_eqVlt [<<-|] /=; [by rewrite phi1|move => lt1m].
  move => /ltzE /ler_eqVlt [<<-|] /=; [by rewrite phi1|move => lt1n].
  move => copmn; rewrite /phi; move: (coprimes_coprime _ _ lt1m lt1n copmn).
  by move/perm_eq_size; rewrite size_map size_allpairs.
qed.

(* ==================================================================== *)
op divisors n = filter (transpose (%|) n) (range 1 (n + 1)).

lemma divisorsP d n :
  d \in divisors n <=> (d %| n /\ d \in range 1 (n + 1)).
proof. by rewrite /divisors mem_filter. qed.

lemma divisors_nil n :
  n <= 0 =>
  divisors n = [].
proof. by move => len0; rewrite /divisors range_geq // -ler_subr_addr. qed.

lemma divisors_mem n k :
  0 < n =>
  k \in divisors n <=> (0 < k /\ k %| n).
proof.
  move => lt0n; rewrite /divisors mem_filter /= andbC; apply/andb_id2r.
  rewrite mem_range ltzS ltzE /= => dvd_; case (1 <= k) => //= le1k; rewrite eqT.
  by move: (dvdz_le _ _ _ dvd_); [apply/gtr_eqF|rewrite !gtr0_norm // ltzE].
qed.

lemma divisors_id n :
  0 < n =>
  n \in divisors n.
proof.
  by move => lt0n; rewrite /divisors rangeSr ?filter_rcons /= ?dvdzz /= ?mem_rcons //; move/ltzE: lt0n.
qed.

lemma divisors1 :
  divisors 1 = [1].
proof. by rewrite /divisors range_ltn // range_geq. qed.

lemma sorted_divisors n :
  sorted Int.(<=) (divisors n).
proof. by apply/(sorted_filter _ ler_trans)/sorted_range. qed.

lemma uniq_divisors n :
  uniq (divisors n).
proof. by apply/filter_uniq/range_uniq. qed.

lemma divisors_prime p :
  prime p =>
  divisors p = [1; p].
proof.
  move => prime_p; rewrite /divisors rangeSr; [by move/ltzE: (gt0_prime _ prime_p)|].
  rewrite filter_rcons /= dvdzz /= -cats1 -(cat1s 1); congr.
  rewrite range_ltn ?gt1_prime //= dvd1z /=; apply/eq_in_filter_pred0 => k mem_ /=.
  case/primeP: prime_p => _ /(_ k _); [by move: mem_; apply/mem_range_incl|].
  rewrite /coprime => eq_1; apply/negP => /dvdzP [q] ->>; move: eq_1.
  by rewrite gcdC gcdMl => /eqr_norml [[|] ->>]; move: mem_; rewrite mem_range.
qed.

lemma divisors_pow_prime p n :
  prime p =>
  0 <= n =>
  divisors (p ^ n) = map (exp p) (range 0 (n + 1)).
proof.
  move => prime_p le0n; apply/(eq_sorted _ ler_trans).
  + by move => ? ? ? ?; apply/ler_anti.
  + by apply/sorted_divisors.
  + apply/sorted_map_in; [|by apply/sorted_range].
    move => x y memx memy le_; apply/ler_weexpn2l; [by apply/ltzW/gt1_prime|].
    by split => //; move: memx; apply/mem_range_le.
  apply/uniq_perm_eq; [by apply/uniq_divisors| |].
  + rewrite map_inj_in_uniq; [|by apply/range_uniq].
    move => x y memx memy; apply/ieexprIn; [by apply/gt0_prime| | |].
    - by apply/gtr_eqF/gt1_prime.
    - by move: memx; apply/mem_range_le.
    by move: memy; apply/mem_range_le.
  move => x; rewrite divisorsP mapP; split.
  + move => [+ mem_range]; rewrite pow_prime_dvd //.
    - by move: mem_range; apply/mem_range_le.
    by case => l; rewrite le2_mem_range => ?; exists l.
  case => l [mem_ ->>]; split; [by apply/dvdz_exp2l/le2_mem_range|].
  apply/mem_range; split; [by apply/ltzS/ltr_subl_addr/expr_gt0/gt0_prime|].
  by move => _; apply/ltzS/ler_weexpn2l; [apply/ltzW/gt1_prime|apply/le2_mem_range].
qed.

lemma divisors_coprime m n :
  0 < m =>
  0 < n =>
  coprime m n =>
  perm_eq (divisors (m * n)) (allpairs Int.( * ) (divisors m) (divisors n)).
proof.
  move => lt0m lt0n copmn; apply/uniq_perm_eq.
  + by apply/uniq_divisors.
  + apply/allpairs_uniq; [by apply/uniq_divisors|by apply/uniq_divisors|].
    move => x1 x2 y1 y2 /divisorsP [dvdx1 memx1] /divisorsP [dvdx2 memx2].
    move => /divisorsP [dvdy1 memy1] /divisorsP [dvdy2 memy2] eq_.
    move: (coprime_gcd_mull x1 y1 n) (coprime_gcd_mull x2 y2 n).
    move: (coprime_gcd_mulr y1 x1 m) (coprime_gcd_mulr y2 x2 m).
    rewrite -eq_ !(coprimeC _ m) (dvdl_coprime _ _ _ dvdx1 copmn).
    rewrite (dvdl_coprime _ _ _ dvdx2 copmn) (dvdr_coprime _ _ _ dvdy1 copmn).
    rewrite (dvdr_coprime _ _ _ dvdy2 copmn) /= => -> + ->.
    rewrite (gcd_dvdl _ _ dvdx1) (gcd_dvdl _ _ dvdx2).
    rewrite (gcd_dvdl _ _ dvdy1) (gcd_dvdl _ _ dvdy2).
    rewrite !ger0_norm //=.
    - by move: memx1; apply/mem_range_le.
    - by move: memx2; apply/mem_range_le.
    - by move: memy1; apply/mem_range_le.
    by move: memy2; apply/mem_range_le.
  move => d; rewrite divisorsP dvdz_mulP allpairsP.
  split => [[[dm dn] [dvdm [dvdn ->>]] mem_]|].
  + exists (`|dm|, `|dn|) => /=; rewrite !divisorsP !dvdz_norml dvdm dvdn /=.
    rewrite -normrM (gtr0_norm (_ * _)%Int) /=; [by move: mem_; apply/mem_range_lt|].
    rewrite !mem_range !ltzS -(gtr0_norm _ lt0m) -(gtr0_norm _ lt0n).
    rewrite !dvdz_le //=; [by apply/gtr_eqF|by apply/gtr_eqF|].
    case/mem_range: (mem_) => + _; rewrite -(gtr0_norm (_ * _)%Int) /=.
    - by move: mem_; apply/mem_range_lt.
    rewrite normrM; case/ler_eqVlt: (normr_ge0 dm) => [/eq_sym/normr0P ->>|lt0_].
    - by rewrite normr0.
    by move/ltzS/ltr_subl_addr/(pmulr_rgt0 _ _ lt0_); move: lt0_; rewrite !ltzE.
  move => [] [dm dn] /= [/divisorsP [dvdm memm]] [/divisorsP [dvdn memn]] ->>.
  split; [by exists dm dn; rewrite dvdm dvdn|].
  move: (mem_range_mul _ _ _ _ _ _ _ _ memm memn) => //=.
  by apply/mem_range_incl => //; apply/lerr_eq; ring.
qed.

lemma sum_phi n :
  0 < n =>
  BIA.big predT phi (divisors n) = n.
proof.
  case/ltzE/ler_eqVlt => [<<-|/=]; [by rewrite divisors1 BIA.big_seq1 phi1|].
  pose P n:= BIA.big predT phi (divisors n) = n; apply/(coprime_ind P); rewrite /P => {P n}.
  + move => p k prime_p lt0k; rewrite divisors_pow_prime ?ltzW // BIA.big_mapT.
    rewrite BIA.big_ltn; [by apply/addr_gt0|]; rewrite {1}/(\o) expr0 phi1 //=.
    rewrite (BIA.eq_big_int _ _ _ (fun n => p ^ n - p ^ (n - 1))).
    - by move => ? [?] _; rewrite /(\o) /= phi_pow_prime // ltzE.
    rewrite -BIA.sumrB; move: (range_add 0 k 1) => /= {2}->.
    rewrite BIA.big_mapT (BIA.eq_big_int 0 _ _ ((^) p)); [by move => ?|].
    rewrite (BIA.big_ltn 0) // expr0 opprD !addrA (addrAC 1) /=.
    move: (rangeSr 1 k _) => /=; [by move/ltzE: lt0k|move => ->].
    by rewrite BIA.big_rcons {1}/predT /= addrAC.
  move => m n lt1m lt1n copmn {2}<- {2}<-.
  move: (divisors_coprime _ _ _ _ copmn); [by apply/ltzE/ltzW|by apply/ltzE/ltzW|].
  move => eq_; rewrite (BIA.eq_big_perm _ _ _ _ eq_) BIA.big_allpairs mulr_big.
  apply/BIA.eq_big_seq => km memm /=; apply/BIA.eq_big_seq => kn memn /=.
  move: memm memn; rewrite !divisors_mem; [by apply/ltzE/ltzW|by apply/ltzE/ltzW|].
  move => [lt0km dvdm] [lt0kn dvdn]; rewrite phi_coprime //.
  by apply/(dvdl_coprime _ _ _ dvdm)/(dvdr_coprime _ _ _ dvdn).
qed.

(* ==================================================================== *)
lemma eq_sizeb_bin n k :
  0 <= k <= n =>
  size (filter (fun t => count idfun t = k) (alltuples n [true; false])) = bin n k.
proof.
case=> le0k lekn; move: (ler_trans _ _ _ le0k lekn) => le0n.
elim: n le0n k le0k lekn => [k le0k lek0|n le0n IHs k le0k lek_].
+ rewrite alltuples_le0 // bin0n; move: (eqz_leq k 0).
  by rewrite le0k lek0 /= => ->> /=; rewrite b2i1.
rewrite alltuplesS //= /allpairs /= cats0 filter_cat size_cat !filter_map !size_map.
case/ler_eqVlt: le0k => [<<-|]; [|move: lek_].
+ move/(_ 0 _ _): IHs => //; rewrite !bin0 // => <-; rewrite eq_in_filter_pred0 /=.
  - by move=> s _; rewrite /preim /idfun /= b2i1 addrC; apply/gtr_eqF/ltzS/count_ge0.
  by congr; apply/eq_filter => ?; rewrite /preim /idfun /= b2i0.
rewrite -(subrK k 1); move: (k - 1) => {k} k /ler_add2r lekn /ltzS le0k.
rewrite binSn // addrC; congr; last first.
+ move: IHs => <- //; congr; apply/eq_filter => ?.
  by rewrite /preim /idfun /= b2i1 addrC; split=> // /addIr.
case/ler_eqVlt: lekn => [->>|ltkn].
+ rewrite bin_gt ?ltzS ?lerr // eq_in_filter_pred0 // => s.
  case/alltuplesP; rewrite ler_maxr // => <<- _.
  by rewrite /preim /= /idfun b2i0 /=; apply/ltr_eqF/ltzS/count_size.
by move: IHs => <- //; [apply/addr_ge0|apply/ltzE].
qed.

lemma perm_eq_subseqs_countb_bin ['a] k (s : 'a list) :
  0 <= k =>
  uniq s =>
  perm_eq
    (filter (transpose subseq s) (alltuples k s))
    (map (transpose mask s) (filter (fun t => count idfun t = k) (alltuples (size s) [true; false]))).
proof.
move=> le0k uniq; case: (leVgt k (size s)) => [lek_|lt_k]; last first.
+ rewrite !eq_in_filter_pred0 //=.
  - move=> t /alltuplesP [] + _; rewrite ler_maxr // => <<-.
    by apply/negP => /subseq_size /lerNgt.
  move=> bs /alltuplesP [] + _; rewrite ler_maxr // => eq_.
  by apply/ltr_eqF/(ler_lt_trans _ _ _ _ lt_k); rewrite -eq_ count_size.
apply/uniq_perm_eq.
+ by apply/filter_uniq/alltuples_uniq.
+ rewrite map_inj_in_uniq; [|by apply/filter_uniq/alltuples_uniq].
  move=> bs1 bs2 /mem_filter /= [] <<- /alltuplesP [] + _.
  rewrite ler_maxr ?size_ge0 // => eq1.
  case/mem_filter => /= /eq_sym eq_ /alltuplesP [] + _.
  by rewrite ler_maxr ?size_ge0 // => eq2; apply/uniq_mask.
move=> t; rewrite mem_filter /= alltuplesP ler_maxr // -subseqP mapP.
split=> [[] [m] [] eq_ ->> [] <<- _ {le0k lek_}|[m] /= []].
+ exists m => /=; rewrite mem_filter /= size_mask //=.
  apply/alltuplesP; rewrite ler_maxr ?size_ge0 // eq_ /=.
  by apply/allP => b _; case: b.
case/mem_filter => /= <<- /alltuplesP; rewrite ler_maxr ?size_ge0 //.
case=> eq_ _ ->>; split; [by exists m|]; split; [by apply/size_mask|].
by apply/allP => ?; apply/mem_mask.
qed.

op mask_to_decr m =
  (foldr (fun b (p : int list * int) => if b then (p.`1, p.`2 + b2i b) else (p.`2 :: p.`1, p.`2)) ([], 0) m).`1.

lemma mask_to_decr_aux_snd m :
  (foldr (fun b (p : int list * int) => if b then (p.`1, p.`2 + b2i b) else (p.`2 :: p.`1, p.`2)) ([], 0) m).`2 =
  count idfun m.
proof.
elim m => //= b m; pose k:= foldr _ _ _; move: k => k ->.
by case b => //= _; rewrite /idfun b2i1 addrC.
qed.

lemma mask_to_decr_nil :
  mask_to_decr [] = [].
proof. by rewrite /mask_to_decr. qed.

lemma mask_to_decr_cons b m :
  mask_to_decr (b :: m) =
  if b
  then mask_to_decr m
  else count idfun m :: mask_to_decr m.
proof. by rewrite /mask_to_decr -mask_to_decr_aux_snd /=; case b; rewrite ?b2i1 ?b2i0. qed.

lemma mask_to_decr_cat m1 m2 :
  mask_to_decr (m1 ++ m2) =
  map ((+) (count idfun m2)) (mask_to_decr m1) ++ mask_to_decr m2.
proof.
elim: m1 => //= b1 m1; rewrite !mask_to_decr_cons /= => ->.
by case b1 => _ //=; rewrite count_cat addrC.
qed.

lemma mask_to_decr_nseqF n :
  mask_to_decr (nseq n false) = nseq n 0.
proof.
case (0 <= n) => [|/ltrNge/ltzW len0]; [|by rewrite !nseq0_le].
elim: n => [|n IHn]; [by rewrite !nseq0|].
by rewrite !nseqS // mask_to_decr_cons /= count_nseq /idfun b2i0.
qed.

lemma mask_to_decr_nseqT n :
  mask_to_decr (nseq n true) = [].
proof.
case (0 <= n) => [|/ltrNge/ltzW len0]; [|by rewrite nseq0_le].
by elim: n => [|n IHn]; [rewrite nseq0|rewrite nseqS].
qed.

lemma maskS m :
  exists n ,
  0 <= n /\
  ( m = nseq n true \/ exists m' , m = nseq n true ++ [false] ++ m').
proof.
elim: m => [|b m]; [by exists 0 => /=; rewrite nseq0|].
case=> n [] le0n; case=> [->>|[m'] ->>].
+ case: b => _; [by exists (n + 1); split; [by apply/addr_ge0|]; left; rewrite nseqS|].
  by exists 0; split=> //; right; exists (nseq n true); rewrite nseq0.
case: b => _; [by exists (n + 1); split; [by apply/addr_ge0|]; right; exists m'; rewrite nseqS|].
by exists 0; split=> //; right; exists (nseq n true ++ [false] ++ m'); rewrite nseq0.
qed.

lemma maskSr m :
  exists n ,
  0 <= n /\
  ( m = nseq n true \/ exists m' , m = m' ++ [false] ++ nseq n true).
proof.
elim/last_ind: m => [|m b]; [by exists 0 => /=; rewrite nseq0|].
case=> n [] le0n; case=> [->>|[m'] ->>].
+ case: b => _; [by exists (n + 1); split; [by apply/addr_ge0|]; left; rewrite nseqSr|].
  by exists 0; split=> //; right; exists (nseq n true); rewrite nseq0 cats0 cats1.
case: b => _; [by exists (n + 1); split; [by apply/addr_ge0|]; right; exists m'; rewrite nseqSr // -!cats1 !catA|].
by exists 0; split=> //; right; exists (m' ++ [false] ++ nseq n true); rewrite nseq0 cats0 -!cats1.
qed.

lemma size_mask_to_decr m :
  size (mask_to_decr m) = size m - count idfun m.
proof.
elim: m => //= b m; rewrite mask_to_decr_cons /= fun_if /= => ->.
by rewrite /(idfun b); case b => _; rewrite ?b2i1 ?b2i0; ring.
qed.

lemma le0_mem_mask_to_decr m k :
  k \in mask_to_decr m => 0 <= k.
proof.
elim: m => //= [|b m]; [by rewrite mask_to_decr_nil|].
rewrite mask_to_decr_cons /=.
by case: b => //= _ IHm; case=> // ->>; apply/count_ge0.
qed.

lemma le_mem_mask_to_decr_range m :
  mem (mask_to_decr m) <= mem (range 0 (count idfun m + 1)).
proof.
move=> k1 mem_; rewrite mem_range (le0_mem_mask_to_decr m) //=.
move: mem_; elim: m => //= [|b m]; [by rewrite mask_to_decr_nil|].
rewrite /(idfun b) mask_to_decr_cons /= => IHm.
case b => [_ /IHm lt_|]; [by apply/(ltr_le_trans _ _ _ lt_); rewrite b2i1 (addrC 1); apply/ltzW/ltzS|].
by move=> _; rewrite b2i0 /=; case=> // ->>; apply/ltzS.
qed.

lemma sorted_mask_to_decr m :
  sorted (transpose Int.(<=)) (mask_to_decr m).
proof.
elim: m => //= b m; rewrite -cat1s mask_to_decr_cat; case b => // _.
move=> sorted_; apply/sorted_cat; [|split].
+ by move=> ? ? ? + ?; apply/ler_trans.
+ move=> x1 x2; rewrite mask_to_decr_cons mask_to_decr_nil /=.
  by move=> ->> /= /le_mem_mask_to_decr_range /mem_range [] _ /ltzS.
by rewrite mask_to_decr_cons mask_to_decr_nil /=.
qed.

lemma inv_mask_to_decr s :
  all ((<=) 0) s =>
  sorted (transpose Int.(<=)) s =>
  exists m , s = mask_to_decr m.
proof.
move=> all_ sorted_.
have: exists k m , s = map (Int.(+) k) (mask_to_decr m); last first.
+ case=> k mm ->>; case: (maskSr mm) => n [] le0n; case=> [->>|[m] ->>].
  - by rewrite mask_to_decr_nseqT /=; exists [].
  rewrite -catA cat1s mask_to_decr_cat mask_to_decr_cons /=.
  rewrite count_nseq /(idfun true) /(idfun false) b2i1 b2i0 /=.
  rewrite mask_to_decr_nseqT ler_maxr // map_cat /=.
  exists (m ++ [false] ++ nseq (k + n) true).
  rewrite -catA cat1s mask_to_decr_cat mask_to_decr_cons /=.
  rewrite count_nseq /(idfun true) /(idfun false) b2i1 b2i0 /=.
  rewrite mask_to_decr_nseqT /= ler_maxr.
  - move/allP/(_ (k + n)): all_ => -> //; apply/mapP; exists n => /=.
    rewrite -catA cat1s mask_to_decr_cat mask_to_decr_cons /=.
    rewrite count_nseq /(idfun true) /(idfun false) b2i1 b2i0 /=.
    by rewrite ler_maxr //= mem_cat.
  by congr; rewrite -map_comp; apply/eq_map => ?; rewrite /(\o); ring.
move: sorted_ => {all_}.
elim: s => [|x s IHs /= path_]; [by exists 0 []|].
case/path_sorted/IHs: (path_) => k m ->> {IHs}; move: path_.
case: (maskS m) => n [] le0n; case=> [->> _|].
+ by rewrite mask_to_decr_nseqT; exists x [false].
move: m => ? [m] ->>; rewrite -catA cat1s.
rewrite mask_to_decr_cat mask_to_decr_cons /=.
rewrite mask_to_decr_nseqT /= => -[] le_ _.
exists k (false :: nseq (x - k - count idfun m) true ++ false :: m) => /=.
rewrite mask_to_decr_cons mask_to_decr_cat mask_to_decr_cons /=.
rewrite count_cat /= count_nseq /(idfun true) /(idfun false) ?b2i1 ?b2i0 /=.
rewrite (addrCA k) -addrA -opprD ler_maxr ?subr_ge0 // subrK /=.
by rewrite mask_to_decr_nseqT.
qed.

lemma inj_mask_to_decr m1 m2 :
  size m1 = size m2 =>
  mask_to_decr m1 = mask_to_decr m2 =>
  m1 = m2.
proof.
move=> size_; pose P m1 m2:= mask_to_decr m1 = mask_to_decr m2 => m1 = m2.
apply/(seq2_sind P) => // {m1 m2 size_} mm1 mm2 size_; rewrite /P => {P} /= IHm.
case: (maskS mm1) => n1 [] le0n1; case=> [->>|[m1] ->>];
(case: (maskS mm2) => n2 [] le0n2; case=> [->>|[m2] ->>]).
+ rewrite !mask_to_decr_nseqT !eq_nseq /=; move: size_.
  by rewrite !size_nseq !ler_maxr.
+ by rewrite -catA cat1s mask_to_decr_cat mask_to_decr_cons /= !mask_to_decr_nseqT.
+ by rewrite -catA cat1s mask_to_decr_cat mask_to_decr_cons /= !mask_to_decr_nseqT.
move: size_; rewrite -!catA !cat1s !mask_to_decr_cat !mask_to_decr_cons /=.
rewrite !mask_to_decr_nseqT /= !size_cat !size_nseq /= !addrA !(addrAC _ 1).
rewrite !ler_maxr // => /addIr + [] count_ mask_; move/(congr1 size): (mask_).
rewrite !size_mask_to_decr count_ => /addIr size_; rewrite size_ => /addIr <<-.
congr; congr; apply/IHm => //; rewrite -catA cat1s size_cat size_nseq /=.
by rewrite ler_maxr // addrA (addrAC _ 1) ltzS; apply/ler_subl_addr.
qed.

lemma perm_eq_undup_perm_eq_countb_bin k n :
  0 <= k =>
  0 < n =>
  perm_eq
    (map (sort (transpose Int.(<=))) (undup_eqv perm_eq (alltuples k (range 0 n))))
    (map mask_to_decr (filter (fun t => count idfun t = n - 1) (alltuples (n + k - 1) [true; false]))).
proof.
move=> le0k lt0n; move: perm_eq_refl<:int> => eq_refl_.
have eq_sym_: symmetric perm_eq<:int> by move=> ??; rewrite perm_eq_sym.
move: perm_eq_trans<:int> => eq_trans_; apply/uniq_perm_eq.
+ rewrite map_inj_in_uniq; [|by apply/undup_eqv_uniq]; move=> s1 s2 mem1 mem2 eq_.
  apply/(mem_undup_eqv_inj _ _ _ _ _ _ _ mem1 mem2) => //.
  - move: eq_; rewrite -perm_sortP //=.
    * by move=> ? ?; apply/ler_total.
    * by move=> ? ? ? + ?; apply/ler_trans.
    by move=> ? ? ? ?; apply/ler_anti.
  rewrite map_inj_in_uniq; [|by apply/filter_uniq/alltuples_uniq].
  move=> m1 m2 /mem_filter /= [] count1 /alltuplesP [] eq1 _.
  move=> /mem_filter /= [] count2 /alltuplesP [] eq2 _.
  by apply/inj_mask_to_decr; rewrite eq1 eq2.
move=> s; rewrite !mapP; split=> [[t] [] + ->>|[m] [] + ->>].
+ case/(mem_undup_eqv _ eq_refl_ eq_sym_ eq_trans_)/hasP => s.
  case=> /alltuplesP [] + all_ perm_; rewrite ler_maxr // => <<- {le0k}.
  case: (inv_mask_to_decr (sort (transpose Int.(<=)) t) _ _).
  - move/perm_eq_sym/perm_eq_all: (perm_sort (transpose Int.(<=)) t) => -> //.
    move/perm_eq_sym/perm_eq_all: perm_ => -> //.
    by move: all_; apply/all_imp_in/allP => ? /= _ /mem_range [].
  - by apply/sort_sorted => ? ? /=; apply/ler_total.
  move=> mm; case: (maskS mm) => i [] le0i; case=> [->>|[m] ->>].
  - rewrite mask_to_decr_nseqT => /(congr1 size); rewrite size_sort size_eq0 => ->> /=.
    exists (nseq (n + size s - 1) true); rewrite mask_to_decr_nseqT /sort /=.
    rewrite mem_filter /= count_nseq /(idfun true) b2i1 /=.
    move/perm_eq_size: perm_ => <- /=; rewrite ler_maxr -?ltzS //=.
    by apply/alltuplesP; rewrite size_nseq /=; apply/allP; case.
  move=> eq_; rewrite eq_; move/(congr1 size): eq_.
  rewrite size_sort size_mask_to_decr !count_cat count_nseq.
  rewrite !size_cat size_nseq /= ler_maxr // /(idfun true) /(idfun false) b2i1 b2i0 /=.
  rewrite opprD !addrA !(addrAC _ _ (-i)) /= -(addrA 1) (addrC 1) => size_.
  exists (nseq (n - count idfun m - 1) true ++ [false] ++ m).
  rewrite -!catA !cat1s !mask_to_decr_cat !mask_to_decr_cons /=.
  rewrite !mask_to_decr_nseqT mem_filter /= count_cat count_nseq /=.
  rewrite /(idfun true) /(idfun false) b2i1 b2i0 /= alltuplesP (eq_all _ predT).
  - by case.
  rewrite all_predT size_cat /= size_nseq (ler_maxr _ (_ + size _ - _)).
  - by rewrite addrAC; apply/addr_ge0; [apply/ltzS|apply/size_ge0].
  move/perm_eq_size: perm_ size_ => -> ->; rewrite ler_maxr; last by split; ring.
  (*TODO: hypothesis missing.*)
  admit.
rewrite mem_filter /= => -[] count_ /alltuplesP [] + _; rewrite ler_maxr.
+ by rewrite addrAC; apply/addr_ge0 => //; apply/ltzS.
move=> size_; pose ss:= undup_eqv _ _.
exists (nth [] ss (find (perm_eq (mask_to_decr m)) ss)).
have has_: has (perm_eq (mask_to_decr m)) ss.
+ rewrite /ss => {ss}.
  rewrite has_r_undup_eqv // hasP; exists (mask_to_decr m).
  rewrite perm_eq_refl /= alltuplesP ler_maxr //.
  rewrite size_mask_to_decr size_ count_; split; [by ring|].
  by apply/allP => x /le_mem_mask_to_decr_range; rewrite count_.
rewrite mem_nth /=; [by rewrite find_ge0 -has_find|].
move/nth_find/(_ []): has_; pose s:= nth _ _ _; move: s => s {ss}.
rewrite (perm_sortP (transpose Int.(<=))) //=.
+ by move=> ? ?; apply/ler_total.
+ by move=> ? ? ? + ?; apply/ler_trans.
+ by move=> ? ? ? ?; apply/ler_anti.
move=> <-; rewrite eq_sym; apply/sort_id => /=.
+ by move=> ? ?; apply/ler_total.
+ by move=> ? ? ? + ?; apply/ler_trans.
+ by move=> ? ? ? ?; apply/ler_anti.
by apply/sorted_mask_to_decr.
qed.

