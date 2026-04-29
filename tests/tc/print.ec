require import AllCore.

(* Regression: `print` must not crash on TC-related entities, and
   abstract type printers must surface their TC constraints. *)
type class addmonoid = {
  op idm : addmonoid
  op (+) : addmonoid -> addmonoid -> addmonoid

  axiom addmA : associative (+)
  axiom addmC : commutative (+)
  axiom add0m : left_id idm (+)
}.

type t <: addmonoid.

print t.
print addmonoid.
print idm.
