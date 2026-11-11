require import AllCore List QFABV.
type W8.
op to_bits : W8 -> bool list.
op from_bits : bool list -> W8.
op of_int : int -> W8.
op to_uint : W8 -> int.
op to_sint : W8 -> int.
bind bitstring to_bits from_bits to_uint to_sint of_int W8 8.
realize gt0_size by admit.
realize tolistP by admit.
realize oflistP by admit.
realize touintP by admit.
realize tosintP by admit.
realize ofintP by admit.
realize size_tolist by admit.

(* [circuit simplify] replaces an equality by [true] when the circuits prove
   it valid, and keeps it otherwise: replacing it by [false] would be
   unsound under a negation. *)
module M = {
  proc f(x : W8) = { return x; }

  proc g(x : W8) = { x <- of_int 0; return x; }

  proc h(x : W8, y : W8) = { y <- x; return y; }
}.

lemma simplify_neg : hoare[M.f : true ==> !(res = of_int 0)].
proof. proc. circuit simplify. fail by trivial. abort.

lemma simplify_valid (x_ : W8) : hoare[M.f : x = x_ ==> res = x_].
proof. proc. circuit simplify. trivial. qed.

(* [extens [x]] substitutes [x] in the postcondition, read in the final
   memory: it requires the program not to write [x]. *)
lemma extens_written : hoare[M.g : x = of_int 1 ==> res = of_int 1].
proof. proc. fail extens [x] : (wp; skip; smt()). abort.

lemma extens_ok (x_ : W8) : hoare[M.h : x = x_ ==> res = x_].
proof. proc. extens [x] : (wp; skip; smt()). qed.
