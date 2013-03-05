require bool.
require import int.

cnst length: int.
axiom length_pos: 0 <= length.

clone bitstring.
type word = bitstring.bitstring.

axiom fixed_length: forall (w:word), length w = length.