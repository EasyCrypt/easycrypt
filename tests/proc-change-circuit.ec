(* -------------------------------------------------------------------- *)
(* Tests for [proc change circuit]: replace a run of program statements
   by an alternative block, with circuit-equivalence as the soundness
   check. *)

require import AllCore List QFABV.

type W8.

op to_bits   : W8 -> bool list.
op from_bits : bool list -> W8.
op of_int    : int -> W8.
op to_uint   : W8 -> int.
op to_sint   : W8 -> int.

bind bitstring to_bits from_bits to_uint to_sint of_int W8 8.
realize gt0_size    by admit.
realize tolistP     by admit.
realize oflistP     by admit.
realize touintP     by admit.
realize tosintP     by admit.
realize ofintP      by admit.
realize size_tolist by admit.

op (+^) : W8 -> W8 -> W8.
bind op W8 (+^) "xor".
realize bvxorP by admit.

module M = {
  proc f (a : W8, b : W8) = {
    var c : W8;
    c <- a +^ b;
    return c;
  }
}.

(* -------------------------------------------------------------------- *)
(* Swap the arguments of an XOR; the replacement is equivalent by
   commutativity. *)
lemma swap_xor_args (a_ b_ : W8) :
  hoare[M.f : a_ = a /\ b_ = b ==> res = a_ +^ b_].
proof.
  proc.
  proc change circuit 1 + 1 { c <- b +^ a; }.
  circuit.
qed.

(* -------------------------------------------------------------------- *)
(* Introduce a fresh local [d] in the replacement block using the
   [[d : W8]] binding list. *)
lemma with_fresh_local (a_ b_ : W8) :
  hoare[M.f : a_ = a /\ b_ = b ==> res = a_ +^ b_].
proof.
  proc.
  proc change circuit [d : W8] 1 + 1 { d <- a; c <- d +^ b; }.
  circuit.
qed.

(* -------------------------------------------------------------------- *)
(* A non-equivalent replacement is rejected: dropping the XOR with [b]
   changes the value written to [c], so the equivalence check refuses
   the rewrite. *)
lemma reject_inequivalent (a_ b_ : W8) :
  hoare[M.f : a_ = a /\ b_ = b ==> res = a_ +^ b_].
proof.
  proc.
  fail proc change circuit 1 + 1 { c <- a; }.
  (* A genuinely equivalent rewrite is accepted, letting the proof close. *)
  proc change circuit 1 + 1 { c <- b +^ a; }.
  circuit.
qed.
