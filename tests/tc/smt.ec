require import AllCore.

type class addmonoid = {
  op idm : addmonoid
  op (+) : addmonoid -> addmonoid -> addmonoid

  axiom addmA : associative (+)
  axiom addmC : commutative (+)
  axiom add0m : left_id idm (+)
}.

(* 1) Concrete instance: SMT pre-reduction collapses TC ops, then smt() closes. *)
op zero_int : int = 0.
op plus_int : int -> int -> int = Int.( + ).

instance addmonoid as int_inst with int
  op idm = zero_int
  op (+) = plus_int.

realize addmA by rewrite /plus_int; smt().
realize addmC by rewrite /plus_int; smt().
realize add0m by rewrite /plus_int /zero_int; smt().

lemma idm_int : (idm<:int>) = zero_int by smt().

(* 2) Abstract carrier: TC class axioms are polymorphic lemmas, instantiated
      explicitly at the per-lemma tparam via [<:'a>]. *)
lemma combine_abs ['a <: addmonoid] (x y : 'a) : (idm + x) + y = x + y.
proof. smt(add0m<:'a>). qed.

lemma triple_assoc ['a <: addmonoid] (x y z w : 'a) :
  ((x + y) + z) + w = x + (y + (z + w)).
proof. smt(addmA<:'a>). qed.

(* 3) TC inheritance: parent axioms instantiated at child carrier. *)
type class addgroup <: addmonoid = {
  op opp : addgroup -> addgroup
  axiom addNm : forall (x : addgroup), opp x + x = idm
}.

lemma group_zero ['a <: addgroup] (x : 'a) : (opp x + x) + idm = idm.
proof. smt(addNm<:'a> add0m<:'a>). qed.

(* 4) Section [declare type t <: tc] reaches SMT correctly. *)
section.
  declare type t <: addmonoid.

  lemma chain (a b c : t) : ((a + idm) + b) + (idm + c) = (a + b) + c.
  proof. smt(add0m<:t> addmA<:t> addmC<:t>). qed.
end section.

(* 5) Two distinct concrete instances coexist in one goal. *)
op zero_bool : bool = false.
op or_bool : bool -> bool -> bool = (\/).

instance addmonoid as bool_inst with bool
  op idm = zero_bool
  op (+) = or_bool.

realize addmA by rewrite /or_bool; smt().
realize addmC by rewrite /or_bool; smt().
realize add0m by rewrite /or_bool /zero_bool; smt().

lemma cross (i : int) (b : bool) :
  zero_int + i = i /\ (zero_bool \/ b = false \/ b).
proof. smt(). qed.
