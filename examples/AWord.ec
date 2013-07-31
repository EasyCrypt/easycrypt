require import Int.

type word.

const length:int.
axiom leq0_length: 0 <= length.

op zeros: word.

op ( ^ ): word -> word -> word.

require import ABitstring.
op to_bits: word -> bitstring.
op from_bits: bitstring -> word.

axiom length_to_bits w:
  `|to_bits w| = length.
axiom can_from_to w:
  from_bits (to_bits w) = w.
axiom pcan_to_from (b:bitstring):
  `|b| = length =>
  to_bits (from_bits b) = b.

theory Dword.
  require import Distr.

  op dword: word distr.
end Dword.