require bool.
require bitstring.
require import int.

cnst k: int.
axiom k_pos: 0 <= k.

clone bitstring as word.
type word = word.bitstring.

axiom fixed_length: forall (w:bitstring), word.length w = k.
