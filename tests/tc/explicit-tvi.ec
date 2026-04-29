require import AllCore.

(* Explicit type-instantiation [<: int>] of a polymorphic-over-TC lemma
   must pick up the matching named instance and succeed. *)
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

lemma idm_idem ['a <: addmonoid] (x : 'a) : idm + x = x.
proof. by apply add0m. qed.

(* Explicit TVI: should pick int_inst. *)
lemma test1 (n : int) : zero_int + n = n.
proof. by apply (idm_idem<:int> n). qed.

(* No TVI: should also work via unification-driven instance resolution. *)
lemma test2 (n : int) : zero_int + n = n.
proof. by apply (idm_idem n). qed.
