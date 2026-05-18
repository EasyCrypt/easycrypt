require import AllCore.

(* Negative: a typeclass body axiom uses a grandparent's TC operator
   without pinning the carrier. The typer must reject with the typed
   "axiom is type-ambiguous" message rather than the raw
   UninstanciateUni anomaly. *)
type class base = {
  op zero : base
  axiom zero_eq : zero = zero
}.

type class tc1 <: base = {
  op f1 : tc1 -> tc1
  axiom f1_id : forall (x : tc1), f1 x = x
}.

type class tc3 <: tc1 = {
  axiom tc3_extra : zero = zero
}.
