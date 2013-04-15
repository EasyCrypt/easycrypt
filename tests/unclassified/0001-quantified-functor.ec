module type J = {
 (* var b:bool *)
}.

module type I(X:J) = {
  fun init(b:bool): unit
  fun get(): bool
}.

module G(X:I) = {
  fun f(): bool = {
    var b:bool;
    X.init(true);
    b := X.get();
    return b;
  }
}.

op c:real.
axiom A: forall &m (M <: I), Pr[ G(M).f() @ &m : res ] = c.
