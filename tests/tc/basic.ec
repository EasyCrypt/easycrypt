require import AllCore.

(* TC declaration with axioms, polymorphic operators and lemmas *)
type class addmonoid = {
  op idm : addmonoid
  op (+) : addmonoid -> addmonoid -> addmonoid

  axiom addmA : associative (+)
  axiom addmC : commutative (+)
  axiom add0m : left_id idm (+)
}.

(* Polymorphic op over a TC *)
op double ['a <: addmonoid] (x : 'a) = x + x.

(* Polymorphic lemma using TC axioms *)
lemma addm0 ['a <: addmonoid] (x : 'a) : x + idm = x.
proof. by rewrite addmC add0m. qed.

(* Section abstracting a TC-constrained type *)
section.
  declare type t <: addmonoid.

  lemma double_id (x : t) : double x = x + x.
  proof. by rewrite /double. qed.

  lemma id_double : double idm<:t> = idm.
  proof. by rewrite /double add0m. qed.
end section.
