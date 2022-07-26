(* ==================================================================== *)
require import AllCore Ring List Int IntMin IntDiv Bigalg Binomial Finite Poly StdBigop.
(*---*) import StdOrder.IntOrder IntID Bigint.BIA.


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
  (forall n , (forall k , k \in range 0 n => P k) => P n) =>
  (forall n , 0 <= n => P n).
proof.
  move => P0 IHS n le0n; elim: n le0n {1 2 4}n (le0n) (lerr n) => [|n le0n IHn] k.
  + by move => le0k lek0; move: (eqz_leq k 0); rewrite lek0 le0k /= => ->>.
  move => le0k /ler_eqVlt [->> {le0k}|/ltzS]; [|by apply/IHn].
  by apply/IHS => k /mem_range [le0k /ltzS lekn]; apply/IHn.
qed.

lemma le_strong_ind P (m : int) :
  P m =>
  (forall n , (forall k , k \in range m n => P k) => P n) =>
  (forall n , m <= n => P n).
proof.
  move => Pm IH n /subr_ge0 le0_; rewrite -(subrK n m).
  move: (n - m) le0_ => +; move => {n} n le0n.
  pose Q n:= P (n + m); apply/(strong_ind Q) => //.
  move => {n le0n} n IHn; rewrite /(Q _); apply/IH.
  move => k mem_; rewrite -(subrK k m); apply/IHn.
  by apply/mem_range_subr.
qed.

lemma lt_strong_ind P (m : int) :
  P (m + 1) =>
  (forall n , (forall k , k \in range (m + 1) n => P k) => P n) =>
  (forall n , m < n => P n).
proof. by move => P_ IH n /ltzE; apply/le_strong_ind. qed.

lemma add_ind P :
  P 1 =>
  (forall m n , 0 < m => 0 < n => P m => P n => P (m + n)) =>
  (forall n , 0 < n => P n).
proof. by move => P1 IHA; apply/lt_ind => // n lt0n Pn; apply/IHA. qed.

(*TODO: move*)
lemma prime2 :
  prime 2.
proof. by apply/primeP => /=; rewrite range_ltn // range_geq. qed.

lemma compositeP n :
  1 < n =>
  ! prime n =>
  exists a b , 1 < a /\ 1 < b /\ n = a * b.
proof.
  move => lt1n; apply/contraR; rewrite negb_exists /= => forall_.
  apply/primeP; split => // a mem_; rewrite /coprime eq_sym.
  apply/gcd_uniq => //=; [by rewrite negb_and gtr_eqF // ltzE ltzW|].
  move => y /dvdzP [x] ->> dvdya; move/(_ x): forall_.
  rewrite negb_exists /= => /(_ y) /= /negb_and; rewrite -!lerNgt.
  case => //; apply/contraLR; rewrite -!ltrNge.
  (*TODO: issue here*)
  admit.
qed.

lemma mul_ind P :
  (forall p , prime p => P p) =>
  (forall m n , 1 < m => 1 < n => P m => P n => P (m * n)) =>
  (forall n , 1 < n => P n).
proof.
  move => Pp IHM; apply/lt_strong_ind => /=.
  + by apply/Pp/prime2.
  move => n IHn; case: (prime n) => [prime_n|Nprime_n]; [by apply/Pp|].
  search _ (!prime _).
  admit.
qed.

lemma coprime_ind P :
  (forall p n , prime p => 0 < n => P (p ^ n)) =>
  (forall m n , 1 < m => 1 < n => coprime m n => P m => P n => P (m * n)) =>
  (forall n , 1 < n => P n).
proof.
  admit.
qed.


(* ==================================================================== *)
op coprimes n = filter (coprime n) (range 1 n).

lemma coprimesP n k :
  k \in coprimes n <=> (coprime n k /\ k \in range 1 n).
proof. by rewrite mem_filter. qed.

lemma coprimes_nil n :
  n <= 1 =>
  coprimes n = [].
proof. by move => ?; rewrite /coprimes range_geq. qed.

lemma coprimes1 n :
  1 < n <=> 1 \in coprimes n.
proof. by rewrite coprimesP /coprime gcdz1 /= mem_range. qed.

lemma coprimes_prime p :
  prime p =>
  coprimes p = range 1 p.
proof. by move => /primeP [lt1p mem_]; rewrite /coprimes eq_in_filter_predT. qed.

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
  n <= 1 =>
  phi n = 0.
proof. by move => len0; rewrite /phi coprimes_nil. qed.

lemma phi_gt0 n :
  1 < n =>
  0 < phi n.
proof. by rewrite /phi -has_predT hasP => /coprimes1 ?; exists 1; rewrite /predT. qed.

lemma phi_ltid n :
  0 < n =>
  phi n < n.
proof.
move => le0n; rewrite /phi /coprimes; apply/(ler_lt_trans (size (range 1 n))).
+ by apply/le_size_filter.
by rewrite size_range ler_maxr; [rewrite -ltzS|rewrite ltzE].
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
  divisors (p ^ n) = map (exp p) (range 0 n).
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
  big predT phi (divisors n) = n - 1.
proof.
  case/ltzE/ler_eqVlt => [<<-|/=]; [by rewrite divisors1 big_seq1 phi_eq0|].
  pose P n:= big predT phi (divisors n) = n - 1; apply/(coprime_ind P); rewrite /P => {P}.
  + move => p k prime_p lt0k; rewrite divisors_pow_prime ?ltzW // big_mapT.
    rewrite big_ltn // {1}/(\o) expr0 phi_eq0 //=.
    rewrite (eq_big_int _ _ _ (fun n => p ^ n - p ^ (n - 1))).
    - by move => ? [?] _; rewrite /(\o) /= phi_pow_prime // ltzE.
    rewrite -sumrB; move: (range_add 0 (k - 1) 1) => /= {2}->.
    rewrite big_mapT (eq_big_int 0 _ _ ((^) p)); [by move => ?|].
    case/ltzE/ler_eqVlt: lt0k => [<<-/=|/= lt1k].
    - rewrite !big_geq // expr1.
      admit.
    rewrite (big_ltn 0) ?ltzS ?subr_gt0 // expr0 opprD addrA addrAC /=.
    move: (rangeSr 1 (k - 1) _) => /=; [by apply/ltzS|move => ->].
    rewrite big_rcons {1}/predT /= (addrAC _ (p ^ _)) /=.
    search _ (_ _ + big _ _ (range _ _)).
    admit.
  admit.
qed.
