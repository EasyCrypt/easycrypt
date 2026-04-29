require import AllCore.

(* Verify SMT pre-reduction unfolds TC ops at concrete instances. *)
type class addmonoid = {
  op idm : addmonoid
  op (+) : addmonoid -> addmonoid -> addmonoid

  axiom addmA : associative (+)
  axiom addmC : commutative (+)
  axiom add0m : left_id idm (+)
}.

op zero_int : int = 0.
op plus_int : int -> int -> int = Int.( + ).

instance addmonoid as int_inst with int
  op idm = zero_int
  op (+) = plus_int.

realize addmA by rewrite /plus_int; smt().
realize addmC by rewrite /plus_int; smt().
realize add0m by rewrite /plus_int /zero_int; smt().

(* SMT pre-reduction collapses [idm<:int>] to [zero_int]; SMT then closes. *)
lemma idm_int : (idm<:int>) = zero_int by smt().
