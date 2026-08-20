require import AllCore.
require import IArray IWord.

(* Symbolic width: XOR is an involutive abelian group. *)
lemma sym_xor_inv {n} (w : word<:n>) : w +^ w +^ w = w.
proof. by rewrite xorwK xorwC xorw0. qed.

lemma sym_and_absorb {n} (w : word<:n>) : andw w w = w.
proof. by apply/andwK. qed.

(* Out-of-range bits are false (the eclib convention). *)
lemma sym_get_out {n} (w : word<:n>) (i : int) : n <= i => w.[i] = false.
proof. by move=> hi; rewrite get_out // ltzNge hi. qed.

(* Concrete width 64: same laws specialise. *)
lemma cn_xorC (w1 w2 : word<:64>) : w1 +^ w2 = w2 +^ w1.
proof. by apply/xorwC. qed.
