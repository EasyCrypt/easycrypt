require        Bool.
require        Bitstring.
require import Int.

cnst k: int.
axiom k_pos: 0 <= k.

clone Bitstring as Word.
export Word.Bits.
export Word.

type word = bitstring.

axiom fixed_length: forall (w:word), length w = k.

(* We can now refine the axioms knowing that the length is fixed. *)
(* This remains to do *)
require        Array.
lemma to_array_length: forall w, Array.length (to_array w) = k.