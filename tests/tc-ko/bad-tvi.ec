require import AllCore.

(* Negative: a TC-polymorphic lemma is instantiated at a type with no
   matching instance. pf_check_tvi must reject this with the typed
   error "type int does not satisfy typeclass constraint addmonoid". *)
type class addmonoid = {
  op idm : addmonoid
  op (+) : addmonoid -> addmonoid -> addmonoid

  axiom addmA : associative (+)
  axiom addmC : commutative (+)
  axiom add0m : left_id idm (+)
}.

lemma idm_idem ['a <: addmonoid] (x : 'a) : idm + x = x.
proof. by apply add0m. qed.

(* No instance for [int]. *)
lemma test : true.
proof.
have := idm_idem<:int> 0.
trivial.
qed.
