require        Bool.
require        Bitstring.
require import Int.

cnst k: int.
axiom k_pos: 0 <= k.

require import Array.
clone Bitstring as Word.
type word = Word.bitstring.

axiom fixed_length: forall (w:word), Word.length w = k.
