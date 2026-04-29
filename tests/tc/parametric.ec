require import AllCore.

(* Parametric typeclass: a class indexed by another typeclass. *)
type class addmonoid = {
  op idm : addmonoid
  op (+) : addmonoid -> addmonoid -> addmonoid

  axiom addmA : associative (+)
  axiom addmC : commutative (+)
  axiom add0m : left_id idm (+)
}.

(* An action of an [addmonoid] on a carrier *)
type class ['a <: addmonoid] action = {
  op act : 'a -> action -> action

  axiom act_id : forall (x : action), act idm<:'a> x = x
}.

(* Polymorphic lemma using the parametric class *)
lemma act_idmE ['a <: addmonoid, 'b <: 'a action] (x : 'b) :
  act idm<:'a> x = x.
proof. by apply act_id. qed.
