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

(* 2) Abstract carrier with TC axiom hints: SMT chains TC axioms through
   the polymorphic operator surface. *)
lemma combine_abs ['a <: addmonoid] (x y : 'a) : (idm + x) + y = x + y.
proof. smt(add0m). qed.

lemma triple_assoc ['a <: addmonoid] (x y z w : 'a) :
  ((x + y) + z) + w = x + (y + (z + w)).
proof. smt(addmA). qed.

(* 2bis) Abstract carrier WITHOUT explicit TC axiom hints: the TC axioms
   tied to the tparam constraint are auto-included by [trans_tc_axioms]. *)
lemma idm_left_nohint ['a <: addmonoid] (x : 'a) : idm + x = x.
proof. smt(). qed.

lemma idm_right_nohint ['a <: addmonoid] (x : 'a) : x + idm = x.
proof. smt(). qed.

(* 3) TC inheritance: parent axioms remain available to SMT. *)
type class addgroup <: addmonoid = {
  op opp : addgroup -> addgroup
  axiom addNm : forall (x : addgroup), opp x + x = idm
}.

lemma group_zero ['a <: addgroup] (x : 'a) : (opp x + x) + idm = idm.
proof. smt(addNm add0m). qed.

(* 3bis) Inheritance + no-hints: parent (addmonoid) axioms must also be
   pulled in via the ancestor walk. *)
lemma group_left_nohint ['a <: addgroup] (x : 'a) : idm + x = x.
proof. smt(). qed.

lemma group_inv_nohint ['a <: addgroup] (x : 'a) : opp x + x = idm.
proof. smt(). qed.

(* 4) Section [declare type t <: tc] reaches SMT correctly. *)
section.
  declare type t <: addmonoid.

  lemma chain (a b c : t) : ((a + idm) + b) + (idm + c) = (a + b) + c.
  proof. smt(add0m addmA addmC). qed.
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
