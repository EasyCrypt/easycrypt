require import Int.

axiom mod_add m n d:
  0 <= m =>
  0 <= n =>
  0 < d =>
  (m + n) %% d = (m %% d) + (n %% d).

lemma mod_mul m d:
  0 <= m =>
  0 < d =>
  (m * d) %% d = 0
by [].

lemma div_def m d q r:
  0 <= m =>
  0 <= d =>
  0 <= q =>
  0 <= r =>
  0 < d =>
  r < d =>
  (m = q * d + r <=>
   (q = m / d /\ r = m %% d)).
proof.
intros=> leq0_m leq0_d {leq0_d} leq0_q leq0_r lt0_d lt_r_d; split; last smt.
intros=> ->; split; first smt.
by rewrite mod_add=> //; smt.
qed.

op (=%): int -> int -> int -> bool.
axiom modeq_def m n d:
  0 <= m => 0 <= n => 0 < d =>
  ((m =% n) d <=> (m %% d = n %% d)).

op (<>%): int -> int -> int -> bool.
axiom modneq_def m n d:
  0 <= m => 0 <= n => 0 < d =>
  ((m <>% n) d <=> (m %% d <> n %% d)).

op (|%): int -> int -> bool.
axiom divides_def d m:
  0 < d => 0 <= m =>
  (m =% 0) d.

lemma divides_bound d m:
  0 < d => 0 < m =>
  d |% m => d <= m.
proof.
intros=> lt0_d leq0_m div_d_m.
cut quotient: exists q, 0 < q => m = d * q by smt.
smt.
qed.

op gcd: int -> int -> int.
  axiom gcd_pos m n:
    0 <= m => 0 <= n =>
    0 < gcd m n.
  axiom gcd_cd m n:
    0 <= m => 0 <= n =>
    gcd m n |% m /\ gcd m n |% n.
  axiom gcd_ub m n d:
    0 <= m => 0 <= n => 0 < d =>
    d |% m => d |% n =>
    d |% gcd m n.
  axiom gcd_bound m n: (* This one should be provable (modulo the case where m = 0) *)
    0 <= m => 0 < n =>
    gcd m n <= min m n.


op egcd: int -> int -> (int * int).
  axiom egcd_def m n km kn:
    0 < m => 0 < n =>
    (km,kn) = egcd m n =>
    km * m + kn * n = gcd m n.
    