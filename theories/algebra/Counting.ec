(* ==================================================================== *)
require import AllCore Ring List Int IntMin IntDiv Bigalg Binomial Finite Poly StdBigop.
(*---*) import StdOrder.IntOrder IntID Bigint.BIA.


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

fail.

lemma dvd_pow_prime p k a :
  prime p =>
  0 <= k =>
  0 <= a =>
  a %| p ^ k <=> (exists l , 0 <= l <= k /\ a = p ^ l).
proof.
move => prime_p le0k le0a; split => [|[l] [? ->>]]; [|by apply/dvdz_exp2l].
elim: k le0k => [|k le0k IHk]; [by rewrite expr0 dvdz1 ger0_norm // => ->>; exists 0; rewrite expr0|].



move => prime_p le0k /ler_eqVlt [<<-|].
+ rewrite dvd0z gtr_eqF /=; [by apply/expr_gt0/gt0_prime|].
  by rewrite negb_exists /= => l; rewrite ltr_eqF //; apply/expr_gt0/gt0_prime.
move => lt0a; case: (pow_prime_divisors _ lt0a) => pps is_ppdec_.
case: (p \in unzip1 pps).
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
  + admit.
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
  rewrite filter_rcons /coprime.
  admit.
qed.

lemma coprimes_prime p :
  prime p =>
  coprimes p = range 1 p.
proof.
  move => /primeP [lt1p mem_]; rewrite /coprimes rangeSr ?ltzW //.
  rewrite filter_rcons eq_in_filter_predT // /coprime.
  admit.
qed.

lemma coprimes_pow_prime p n :
  prime p =>
  0 <= n =>
  coprimes (p ^ (n + 1)) = flatten (mkseq (fun k => map (Int.(+) k) (coprimes (p ^ n))) p).
proof.
  move => prime_p le0n.
  admit.
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
move => /coprimes_subseq; rewrite /phi.
(*TODO: missing*)
search _ subseq size.
admit.
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
  admit.
qed.

lemma phi_coprime m n :
  0 < m =>
  0 < n =>
  coprime m n =>
  phi (m * n) = phi m * phi n.
proof.
  admit.
qed.

(* ==================================================================== *)
op divisors n = filter (transpose (%|) n) (range 1 (n + 1)).

lemma divisors_nil n :
  n <= 0 =>
  divisors n = [].
proof. by move => len0; rewrite /divisors range_geq // -ler_subr_addr. qed.

lemma divisors_mem n :
  0 < n =>
  n \in divisors n.
proof. by move => lt0n; rewrite /divisors rangeSr ?filter_rcons /= ?dvdzz /= ?mem_rcons //; move/ltzE: lt0n. qed.

lemma divisors1 :
  divisors 1 = [1].
proof. by rewrite /divisors range_ltn // range_geq. qed.

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
  admit.
qed.

lemma divisors_coprime m n :
  0 < m =>
  0 < n =>
  coprime m n =>
  perm_eq (divisors (m * n)) (allpairs Int.( * ) (divisors m) (divisors n)).
proof.
  admit.
qed.

lemma sum_phi n :
  0 < n =>
  big predT phi (divisors n) = n.
proof.
  case/ltzE/ler_eqVlt => [<<-|/=]; [by rewrite divisors1 big_seq1 phi1|].
  pose P n:= big predT phi (divisors n) = n; apply/(coprime_ind P); rewrite /P => {P}.
  + move => p k prime_p lt0k; rewrite divisors_pow_prime ?ltzW // big_mapT.
    rewrite big_ltn; [by apply/addr_gt0|]; rewrite {1}/(\o) expr0 phi1 //=.
    rewrite (eq_big_int _ _ _ (fun n => p ^ n - p ^ (n - 1))).
    - by move => ? [?] _; rewrite /(\o) /= phi_pow_prime // ltzE.
    rewrite -sumrB; move: (range_add 0 k 1) => /= {2}->.
    rewrite big_mapT (eq_big_int 0 _ _ ((^) p)); [by move => ?|].
    rewrite (big_ltn 0) // expr0 opprD !addrA (addrAC 1) /=.
    move: (rangeSr 1 k _) => /=; [by move/ltzE: lt0k|move => ->].
    by rewrite big_rcons {1}/predT /= addrAC.
  admit.
qed.
