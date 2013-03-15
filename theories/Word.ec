require        Bool.
require import Bitstring.
require import Int.

cnst k: int.
axiom k_pos: 0 <= k.

clone Bitstring as Word.
export Bitstring.

type word = Word.bitstring.

axiom fixed_length: forall (w:word), Word.length w = k.
