require import AllCore.

(* A section using [declare type t <: tc] for an abstract carrier; the
   developed operators survive section close as TC-polymorphic. *)
type class addmonoid = {
  op idm : addmonoid
  op (+) : addmonoid -> addmonoid -> addmonoid

  axiom addmA : associative (+)
  axiom addmC : commutative (+)
  axiom add0m : left_id idm (+)
}.

section.
  declare type t <: addmonoid.

  op double (x : t) : t = x + x.

  lemma double_idm : double idm = idm.
  proof. by rewrite /double add0m. qed.
end section.

(* After section close: [double] becomes TC-polymorphic. *)
op test_call ['a <: addmonoid] (x : 'a) : 'a = double x.

lemma test_idm ['a <: addmonoid] : double<:'a> idm = idm.
proof. by apply double_idm. qed.
