require import AllCore.

(* Test that multiple named instances for the same TC at different
   types coexist without interference. *)
type class addmonoid = {
  op idm : addmonoid
  op (+) : addmonoid -> addmonoid -> addmonoid

  axiom addmA : associative (+)
  axiom addmC : commutative (+)
  axiom add0m : left_id idm (+)
}.

(* Instance for [int] *)
op zero_int : int = 0.
op plus_int : int -> int -> int = Int.( + ).

instance addmonoid as int_inst with int
  op idm = zero_int
  op (+) = plus_int.

realize addmA by rewrite /plus_int; smt().
realize addmC by rewrite /plus_int; smt().
realize add0m by rewrite /plus_int /zero_int; smt().

(* Both instance types coexist; explicit instantiation picks the right one *)
op test_int  : int  = idm<:int>.

lemma test_int_eq : test_int = zero_int by rewrite /test_int; smt().
