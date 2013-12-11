module type I = {
  proc init(b:bool): unit
  proc get(): bool
}.

module G(X:I) = {
  proc f(): bool = {
    var b:bool;
    X.init(true);
    b  = X.get();
    return b;
  }
}.

op c:real.
axiom A: forall &m (M <: I), Pr[ G(M).f() @ &m : res ] = c.
