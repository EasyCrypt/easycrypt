(* Regression test for issue #989.

   Overriding a datatype's type with another datatype (`type ATy = ...`)
   used to crash with `anomaly: ... Assertion failed` when an operator body
   referenced one of the source datatype's constructors. The replay machinery
   only redirected the source constructors to the target's constructors for
   inline overrides (`<-`/`<=`), so for a plain alias (`=`) the constructor
   references were renamed to non-existent paths and tripped an `oget None`.

   Both override modes must accept this clone. *)

theory Thy.
  type ATy = [ CA | CB of int & bool ].
  op mk = CB 3 true.
  op base = CA.
end Thy.

clone Thy as Thy1.

(* plain alias override (the form that used to crash) *)
clone Thy as Thy2 with
  type ATy = Thy1.ATy,
  op mk   <= Thy1.mk,
  op base <= Thy1.base.

(* inline override (already worked; kept as a companion check) *)
clone Thy as Thy3 with
  type ATy <- Thy1.ATy,
  op mk   <= Thy1.mk,
  op base <= Thy1.base.
