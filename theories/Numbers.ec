require import Int.

op (=%): int -> int -> int -> bool.
axiom modeq_def m n d:
  0 <> d =>
  ((m =% n) d <=> (m %% d = n %% d)).

op (<>%): int -> int -> int -> bool.
axiom modneq_def m n d:
  0 <> d =>
  ((m <>% n) d <=> (m %% d <> n %% d)).

op (|%): int -> int -> bool.
axiom divides_def d m:
  0 <> d =>
  (d |% m <=> (m =% 0) d).

axiom mod_mod m d:
  0 <> d =>
  (m %% d) %% d = m %% d.

axiom mod_add m n d:
  0 <> d =>
  ((m + n) %% d =% (m %% d) + (n %% d)) d.

lemma mod_mul m d:
  0 < d =>
  (m * d) %% d = 0
by [].

lemma div_def m d q r:
  0 <> d =>
  0 <= r < d =>
  (m = q * d + r <=>
   (q = m / d /\ r = m %% d)).
proof.
intros=> lt0_d [leq0_r lt_r_d]; split; last smt.
intros=> ->; split; smt.
qed.

lemma nosmt divides_0 d:
  0 <> d => d |% 0
by [].

axiom divides_bound d m:
  0 <> d => 0 <> m =>
  d |% m => `|d| <= `|m|.

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