require import AllCore.

(* Abstract theory parametrized by a TC carrier; cloning the theory
   with a concrete carrier must thread the TC instance correctly. *)
type class addmonoid = {
  op idm : addmonoid
  op (+) : addmonoid -> addmonoid -> addmonoid

  axiom addmA : associative (+)
  axiom addmC : commutative (+)
  axiom add0m : left_id idm (+)
}.

abstract theory T.
  type t <: addmonoid.

  op double (x : t) : t = x + x.

  lemma double_idm : double idm = idm.
  proof. by rewrite /double add0m. qed.
end T.

(* Concrete instance for [int]. *)
op zero_int : int = 0.
op plus_int : int -> int -> int = Int.( + ).

instance addmonoid as int_inst with int
  op idm = zero_int
  op (+) = plus_int.

realize addmA by rewrite /plus_int; smt().
realize addmC by rewrite /plus_int; smt().
realize add0m by rewrite /plus_int /zero_int; smt().

(* Clone T with t = int. The carrier's TC constraint is satisfied by
   int_inst. The cloned theory's lemmas/ops are usable. *)
clone T as TI with type t = int.

(* Cloned operator [TI.double] is well-typed at the concrete carrier. *)
op test_op : int = TI.double zero_int.

(* Cloned op reduces under [delta_tc] using the resolved concrete instance. *)
lemma test_double : TI.double zero_int = plus_int zero_int zero_int.
proof. by rewrite /TI.double. qed.
