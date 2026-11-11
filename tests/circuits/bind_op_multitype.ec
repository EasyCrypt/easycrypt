(* Extracted from doc/tactics/bindings.rst -- "Operator Binding Example (multi-type)". *)

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

op bool2bits (b : bool) : bool list = [b].
op bits2bool (b : bool list) : bool = List.nth false b 0.
op i2b : int -> bool.
op b2si (b : bool) = 0.

bind bitstring bool2bits bits2bool b2i b2si i2b bool 1.
realize gt0_size by done.
realize size_tolist by auto.
realize tolistP by auto.
realize oflistP by rewrite /bool2bits /bits2bool; smt(size_eq1).
realize touintP by admit.
realize tosintP by done.
realize ofintP by admit.

op "_.[_]" : W8 -> int -> bool.

bind op [W8 & bool] "_.[_]" "get".
realize le_size by auto.
realize eq1_size by auto.
realize bvgetP by admit.
