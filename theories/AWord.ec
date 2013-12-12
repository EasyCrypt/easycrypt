require import Int.
require import FSet.

type word.

const length:int.
axiom leq0_length: 0 <= length.

op zeros: word.
op ones: word.

op ( ^ ): word -> word -> word.

axiom xorwA (w1 w2 w3:word):
  w1 ^ (w2 ^ w3) = (w1 ^ w2) ^ w3.
axiom xorwC (w1 w2:word):
  w1 ^ w2 = w2 ^ w1.
axiom xorw0 (w:word):
  w ^ zeros = w.
axiom xorwK (w:word):
  w ^ w = zeros.

require export ABitstring.
op to_bits: word -> bitstring.
op from_bits: bitstring -> word.

axiom length_to_bits w:
  `|to_bits w| = length.
axiom can_from_to w:
  from_bits (to_bits w) = w.
axiom pcan_to_from (b:bitstring):
  `|b| = length =>
  to_bits (from_bits b) = b.

(** Conversion with int *)
op to_int   : word -> int.
op from_int : int -> word.

axiom to_from w: from_int (to_int w) = w.
axiom from_to i: to_int (from_int i) = i %% 2^length.

lemma from_to_bound i:
   0 <= i < 2^length =>
   to_int (from_int i) = i.
proof -strict.
 rewrite from_to.
 intros H.
 elim (EuclDiv.ediv_unique i (2^length) 0 i _ _ _) => //;first 2 smt.
 by intros _ <-.
qed.

theory Dword.
  require import Distr.
  require import Real.

  op dword: word distr.
  axiom mu_x_def w: mu_x dword w = 1%r/(2^length)%r.
  axiom lossless: weight dword = 1%r.

  lemma in_supp_def w: in_supp w dword.
  proof -strict.
  by rewrite /in_supp mu_x_def; smt.
  qed.

  lemma mu_cpMemw X:
    mu dword (cpMem X) = (card X)%r / (2^length)%r.
  proof -strict.
  by rewrite (mu_cpMem _ _ (1%r/(2^length)%r))=> // x;
     rewrite mu_x_def.
  qed.

  import FSet.Dexcepted.
  lemma lossless_restrw X:
    card X < 2^length =>
    weight (dword \ X) = 1%r.
  proof -strict.
  intros=> card_X; rewrite lossless_restr ?lossless // ?mu_cpMemw;
  cut <-: (forall x y, x * (1%r / y) = x / y) by smt;
  apply (real_lt_trans _ ((2^length)%r* (1%r/(2^length)%r)) _); last smt.
  apply mulrM; last by rewrite from_intM.
  smt.
  qed.
end Dword.