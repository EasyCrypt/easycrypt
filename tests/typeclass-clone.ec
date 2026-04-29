require import AllCore.

(* Cloning a theory containing a typeclass and a TC-polymorphic lemma *)
abstract theory Algebra.
  type class addmonoid = {
    op idm : addmonoid
    op (+) : addmonoid -> addmonoid -> addmonoid

    axiom addmA : associative (+)
    axiom addmC : commutative (+)
    axiom add0m : left_id idm (+)
  }.

  lemma addm0 ['a <: addmonoid] (x : 'a) : x + idm = x.
  proof. by rewrite addmC add0m. qed.
end Algebra.

(* The cloned typeclass and lemma are usable in the cloned theory *)
clone Algebra as A2.

op test ['a <: A2.addmonoid] (x : 'a) = A2.(+) x A2.idm.

lemma test_eq ['a <: A2.addmonoid] (x : 'a) : test x = x.
proof. rewrite /test. exact A2.addm0. qed.
