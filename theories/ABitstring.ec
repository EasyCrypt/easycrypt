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

axiom zeros_ones l : 0 < l => zeros l <> ones l.

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

axiom app1 l l':
  0 <= l => 0 <= l' =>
  (ones l || ones l') = ones (l + l').

axiom appI (a b b':bitstring):
  (a || b) = (a || b') =>
  b = b'.

axiom appA (x1 x2 x3:bitstring):
     ((x1 || x2) || x3) = (x1 || (x2 || x3)).

(* TODO: remane it a a form of distributivity *)
axiom app_xor_interchange (a b a' b':bitstring):
  `|a| = `|a'| => `|b| = `|b'| =>
  ((a ^ a') || (b ^ b')) = (a || b) ^ (a' || b').

op sub: bitstring -> int -> int -> bitstring.

axiom length_sub (a:bitstring) (s l:int):
  0 <= s => 0 <= l => s + l <= `|a| =>
  `|sub a s l| = l.

axiom sub_full : forall (xs:bitstring),
  sub xs 0 `|xs| = xs.

axiom sub_app_fst_le (b1 b2:bitstring) x l:
   0 <= x => 0 <= l => x + l <= `|b1| =>
    sub (b1 || b2) x l = sub b1 x l.

axiom sub_app_snd_le (b1 b2:bitstring) x l:
  `|b1| <= x => 
   sub (b1 || b2) x l = sub b2 (x - `|b1|) l.

axiom sub_app_sub: forall (xs:bitstring, i l1 l2:int),
  0 <= i => 0 <= l1 => 0 <= l2 => i+l1+l2 <= `|xs| =>
  (sub xs i l1 || sub xs (i+l1) l2) = sub xs i (l1+l2).

lemma sub_app_fst (b1 b2:bitstring):
  sub (b1 || b2) 0 `|b1| = b1.
proof.
  rewrite sub_app_fst_le //;[apply lengthP | apply sub_full].
save.

lemma sub_app_snd(b1 b2:bitstring):
  sub (b1 || b2) `|b1| `|b2| = b2.
proof.
  rewrite sub_app_snd_le //;smt.
save.

lemma app_sub (b:bitstring) l1 l2:
  0 <= l1 => 0 <= l2 => l1 + l2 = `|b| =>
  ((sub b 0 l1) || (sub b l1 l2)) = b.
proof.
 intros Hl1 Hl2 Hb;rewrite {2}(_:l1 = 0 + l1);first smt.
 rewrite sub_app_sub //;first smt.
 rewrite Hb;apply sub_full.
qed.

lemma sub_sub (b:bitstring) s1 l1 s2 l2:
  0 <= s1 => 0 <= l1 => s1 + l1 <= `|b| =>
  0 <= s2 => 0 <= l2 => s2 + l2 <= l1 =>
  sub (sub b s1 l1) s2 l2 = sub b (s1 + s2) l2.
proof.
  intros Hs1 Hl1 Hb Hs2 Hl2 Hsll.
  rewrite {1}(_: b = (sub b 0 s1 || sub b s1 s2 || 
           sub b (s1+s2) l2 || sub b (s1+s2+l2) (l1-(l2+s2)) || 
           sub b (s1+s2+l2+(l1-(l2+s2))) (`|b|-(s1+l1)))).
    rewrite sub_app_sub //; first 4 smt.
    by rewrite sub_app_sub //;smt.
  rewrite sub_app_snd_le;first smt.
  rewrite (_:s1 - `|sub b 0 s1| = 0);first smt.
  rewrite - ?appA.
  rewrite sub_app_fst_le //;first smt.
  rewrite {2} (_:l1 = `|((sub b s1 s2 || sub b (s1 + s2) l2) ||
      sub b (s1 + s2 + l2) (l1 - (l2 + s2)))|);first by smt.
  rewrite sub_full ?appA.
  rewrite sub_app_snd_le //; first smt.
  rewrite (_:s2 - `|sub b s1 s2| = 0);first smt.
  rewrite sub_app_fst_le //;smt.
qed.

theory DBitstring.
  require import Distr.

  op dbitstring: int -> bitstring distr.
end DBitstring.