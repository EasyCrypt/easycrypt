require import Int.
require import Real.

lemma sum_ex (a : int) (b : real): exists (c:real), a%r+b=c.
proof. by exists (a%r + b). qed.

choice sum with sum_ex.

lemma test: sum 0 0%r = 0%r.
proof. admit. qed.
