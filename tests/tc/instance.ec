require import AllCore Bool.

(* TC + named instance for a concrete type *)
type class addmonoid = {
  op idm : addmonoid
  op (+) : addmonoid -> addmonoid -> addmonoid

  axiom addmA : associative (+)
  axiom addmC : commutative (+)
  axiom add0m : left_id idm (+)
}.

instance addmonoid as bool_xor with bool
  op idm = false
  op (+) = (^^).

realize addmA by smt().
realize addmC by smt().
realize add0m by smt().

(* Use the polymorphic ops at the concrete instance type. The instance
   resolution must succeed (otherwise the typing would fail). *)
op test (x : bool) = x + idm<:bool>.

(* Unnamed instance also works (auto-named) *)
type class group <: addmonoid = {
  op opp : group -> group
  axiom addmN : left_inverse idm opp (+)<:group>
}.
