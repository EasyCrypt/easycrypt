(* Extracted from doc/tactics/circuit.rst -- "Hoare logic example". *)

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

(* The realizes below discharge the side conditions left by
   [bind bitstring]; refer to the [bind] command documentation. *)
realize gt0_size by admit.
realize tolistP by admit.
realize oflistP by admit.
realize touintP by admit.
realize tosintP by admit.
realize ofintP by admit.
realize size_tolist by admit.

op (+^) : W8 -> W8 -> W8.
bind op W8 (+^) "xor".
realize bvxorP by admit.

module M = {
  proc f(w : W8) = {
    return w +^ w;
  }
}.

lemma L (w_ : W8) : hoare[M.f : w_ = w ==> res = of_int 0].
proof.
  proc. circuit.
abort.
