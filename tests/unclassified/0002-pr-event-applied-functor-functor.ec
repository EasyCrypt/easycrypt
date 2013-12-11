(* FIXME: disabled - this test is a non-sense

module type I = {
  proc init(b:bool): unit
  proc get(): bool
}.

module type J = {
  proc f() : bool
}.

module G(X:I) : J = {
  proc f(): bool = {
    var b:bool;
    X.init(true);
    b  = X.get();
    return b;
  }
}.

op c:real.

axiom A: forall &m (M' <: I(M)), Pr[G(M').f() @ &m : res] = c.
*)
