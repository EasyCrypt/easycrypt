theory T.
  theory Sub.
    type t.

    cnst myop : t -> bool.

    axiom A : forall t, myop t.
  end Sub.
end T.

clone T.Sub as U.

type t = U.t.


require bool.
require bitstring.
require import int.

cnst length: int.
axiom length_pos: 0 <= length.

clone bitstring.
type word = bitstring.bitstring.

axiom fixed_length: forall (w:word), length w = length.
