require import AllCore.

(* Multi-level subclass chain: addmonoid <- group, with a polymorphic
   lemma at the parent level used through the subclass. *)
type class addmonoid = {
  op idm : addmonoid
  op (+) : addmonoid -> addmonoid -> addmonoid

  axiom addmA : associative (+)
  axiom addmC : commutative (+)
  axiom add0m : left_id idm (+)
}.

type class group <: addmonoid = {
  op opp : group -> group
  axiom addmN : left_inverse idm opp (+)<:group>
}.

(* Polymorphic lemma over [addmonoid] *)
lemma addm0 ['a <: addmonoid] (x : 'a) : x + idm = x.
proof. by rewrite addmC add0m. qed.

(* The same lemma should be usable under the [group] subclass — the
   ancestor walk surfaces the [addmonoid] constraint. *)
lemma addm0_via_group ['a <: group] (x : 'a) : x + idm = x.
proof. by apply addm0. qed.

(* And direct use of the parent operator on a subclass-bound value. *)
op test ['a <: group] (x : 'a) : 'a = x + idm + opp x.
