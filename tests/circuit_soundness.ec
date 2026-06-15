(* ==================================================================== *)
(* Regression tests for circuit-tactic soundness fixes.                 *)
(*                                                                       *)
(* Each [fail <tac>] asserts that a previously-UNSOUND acceptance is now *)
(* rejected: if the bug regresses, the inner tactic succeeds and [fail]  *)
(* turns that into a test failure. The positive lemmas guard that the    *)
(* fixes did not cost completeness.                                      *)
(*                                                                       *)
(* History: all three [fail] lemmas below used to close (proving false   *)
(* facts) -- see commits 0357c262a (proc change circuit), ab3159f81      *)
(* (uninitialized locals) and 080d9af3d (witness).                       *)
(* ==================================================================== *)
require import AllCore List QFABV IntDiv.

type W8.
op to_bits : W8 -> bool list.  op from_bits : bool list -> W8.
op of_int : int -> W8.         op to_uint : W8 -> int.  op to_sint : W8 -> int.
bind bitstring to_bits from_bits to_uint to_sint of_int W8 8.
realize gt0_size by admit.  realize tolistP by admit.  realize oflistP by admit.
realize touintP by admit.   realize tosintP by admit.  realize ofintP by admit.
realize size_tolist by admit.

op (+^) : W8 -> W8 -> W8.  bind op W8 (+^) "xor".  realize bvxorP by admit.
op zero : W8 = of_int 0.

(* -------------------------------------------------------------------- *)
(* proc change circuit must REJECT a non-equivalent rewrite. The check   *)
(* used to collapse all program variables to one input, so [c <- a +^ b] *)
(* and the constant [c <- zero] looked equivalent.                       *)
module M = {
  proc f (a b : W8) : W8 = {
    var c : W8;
    c <- a +^ b;
    return c;
  }
}.

lemma pcc_reject_unsound : hoare[M.f : true ==> res = zero].
proof.
  proc.
  fail proc change circuit 1 + 1 { c <- zero; }.
abort.

(* A genuinely equivalent rewrite is still accepted (no over-rejection). *)
lemma pcc_accept_equiv (a_ b_ : W8) :
  hoare[M.f : a_ = a /\ b_ = b ==> res = a_ +^ b_].
proof.
  proc.
  proc change circuit 1 + 1 { c <- b +^ a; }.
  circuit.
qed.

(* -------------------------------------------------------------------- *)
(* circuit must not prove false facts about uninitialized locals. [x]    *)
(* and [y] used to collapse to one shared input, so [x +^ y] looked 0.   *)
module G = {
  proc g () : W8 = {
    var x : W8;
    var y : W8;
    var z : W8;
    z <- x +^ y;
    return z;
  }
}.

lemma uninit_reject : hoare[G.g : true ==> res = zero].
proof. proc. fail circuit. abort.

(* -------------------------------------------------------------------- *)
(* circuit must not equate the (independent) components of an arbitrary  *)
(* value. A witness used to be one shared bit, so its bits were equal.   *)
lemma witness_reject : (witness<:W8 * W8>).`1 = (witness<:W8 * W8>).`2.
proof. fail circuit. abort.

(* Completeness: a witness still equals itself, and xors to zero with    *)
(* itself (the fix shares identical witness forms via the form cache).   *)
lemma witness_refl : witness<:W8> = witness<:W8>.
proof. circuit. qed.

lemma witness_xor_self : witness<:W8> +^ witness<:W8> = zero.
proof. circuit. qed.

(* -------------------------------------------------------------------- *)
(* Completeness: a circuit-typed term with no structural translation     *)
(* (a free variable, or an application of an opaque head) is an opaque   *)
(* leaf modelled as a fresh, form-cached input -- not a [Not_found]      *)
(* anomaly. Alpha-equal occurrences share their input.                   *)
theory A.
  type 'a t.
  op tolist : 'a t -> 'a list.
  op oflist : 'a -> 'a list -> 'a t.
  op "_.[_]"    : 'a t -> int -> 'a.
  op "_.[_<-_]" : 'a t -> int -> 'a -> 'a t.
end A.
bind array A."_.[_]" A."_.[_<-_]" A.tolist A.oflist A.t 8.
realize gt0_size by admit.  realize tolistP by admit.  realize oflistP by admit.
realize eqP by admit.  realize get_setP by admit.  realize get_out by admit.
export A.

op init (f : int -> W8) : W8 A.t.
bind op [W8 & A.t] init "ainit".
realize bvainitP by admit.

(* [(init f).[4]] applies the opaque [f] at index 4; both that occurrence *)
(* and the right-hand [f 4] resolve to the same cached input.            *)
lemma opaque_app_shared (f : int -> W8) : (init f).[4] = f 4.
proof. circuit. qed.

lemma opaque_app_xor_self (f : int -> W8) : f 4 +^ f 4 = zero.
proof. circuit. qed.

(* A free variable of circuit type is itself an opaque leaf. *)
lemma free_var_refl (x : W8) : x = x.
proof. circuit. qed.

(* Soundness of the sharing: DISTINCT opaque leaves get DISTINCT inputs,  *)
(* so non-alpha-equal terms must NOT be equated.                         *)
lemma opaque_app_distinct (f : int -> W8) : f 4 = f 5.
proof. fail circuit. abort.

lemma free_var_distinct (x y : W8) : x = y.
proof. fail circuit. abort.
