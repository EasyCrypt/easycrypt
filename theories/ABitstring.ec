require import Int.

type bitstring.
op "`|_|": bitstring -> int.
axiom lengthP (b:bitstring): 0 <= `|b|.

op zeros: int -> bitstring.
axiom length_zeros l:
  0 <= l => `|zeros l| = l.

op ones: int -> bitstring.
axiom length_ones l:
  0 <= l => `|ones l| = l.

op ( ^ ): bitstring -> bitstring -> bitstring.
axiom length_xor (b:bitstring):
  `|b ^ b| = `|b|.
axiom xorA (a b c:bitstring):
  `|a| = `|b| => `|b| = `|c| =>
  a ^ (b ^ c) = (a ^ b) ^ c.
axiom xorC (a b:bitstring):
  `|a| = `|b| =>
  a ^ b = b ^ a.
axiom xor0 (b:bitstring): b ^ zeros `|b| = b.
axiom xorN (b:bitstring): b ^ b = zeros `|b|.

(*
lemma xorI (a b b':bitstring):
  `|a| = `|b| => `|b| = `|b'| =>
  a ^ b = a ^ b' => b = b'.
proof.
intros=> eql_a_b eql_b_b' eq_axor;
rewrite -xor0 -(xor0 b') -eql_b_b' -eql_a_b -xorN
        ?(xorC _ (a ^ a)) ?length_xor - ?eql_b_b' ?eql_a_b //
        -2?xorA - ?eql_b_b' //
        (fcongr ((^) a) (a ^ b) (a ^ b')) //.
qed. *)

op (||): bitstring -> bitstring -> bitstring.
axiom length_app (a b:bitstring):
  `|(a || b)| = `|a| + `|b|.
axiom app0 l l':
  0 <= l => 0 <= l' =>
  (zeros l || zeros l') = zeros (l + l').
axiom appI (a b b':bitstring):
  (a || b) = (a || b') =>
  b = b'.

axiom app_xor_interchange (a b a' b':bitstring):
  `|a| = `|a'| => `|b| = `|b'| =>
  ((a ^ a') || (b ^ b')) = (a || b) ^ (a' || b').

op sub: bitstring -> int -> int -> bitstring.
axiom length_sub (a:bitstring) (s l:int):
  0 <= s => 0 <= l => s + l <= `|a| =>
  `|sub a s l| = l.

axiom sub_app_fst (b1 b2:bitstring):
  sub (b1 || b2) 0 `|b1| = b1.
axiom sub_app_snt (b1 b2:bitstring):
  sub (b1 || b2) `|b1| `|b2| = b2.

axiom app_sub (b:bitstring) l1 l2:
  0 <= l1 => 0 <= l2 => l1 + l2 = `|b| =>
  ((sub b 0 l1) || (sub b l1 l2)) = b.

theory DBitstring.
  require import Distr.

  op dbitstring: int -> bitstring distr.
end DBitstring.