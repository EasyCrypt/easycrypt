require import AllCore.

(* Using a grandparent's TC operator inside a typeclass body. The
   carrier is implicit, so we must pin it via [<:carrier>] when the
   operator's argument types do not otherwise force the carrier. *)
type class base = {
  op zero : base
  axiom zero_eq : zero = zero
}.

type class tc1 <: base = {
  op f1 : tc1 -> tc1
  axiom f1_id : forall (x : tc1), f1 x = x
}.

(* Without explicit tvi, the typer cannot infer the carrier and emits a
   clear "type-ambiguous" error. The standard fix is to pin the
   carrier with [<:carrier>]. *)
type class tc3 <: tc1 = {
  axiom tc3_extra : (zero<:tc3>) = zero
}.

(* When the operator's argument forces the carrier, no explicit tvi is
   needed: [zero = x] implies [zero : tc3_alt] from [x : tc3_alt]. *)
type class tc3_alt <: tc1 = {
  axiom tc3_via_arg : forall (x : tc3_alt), zero = x => x = zero
}.
