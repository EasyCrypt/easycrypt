(* Extracted from doc/tactics/bindings.rst -- "Bitstring Binding Example". *)

require import AllCore List QFABV.

type W8.

op to_bits : W8 -> bool list.
op from_bits : bool list -> W8.
op of_int : int -> W8.
op to_uint : W8 -> int.
op to_sint : W8 -> int.

bind bitstring
  to_bits
  from_bits
  to_uint
  to_sint
  of_int
  W8
  8.

realize gt0_size by admit.
realize tolistP by admit.
realize oflistP by admit.
realize touintP by admit.
realize tosintP by admit.
realize ofintP by admit.
realize size_tolist by admit.
