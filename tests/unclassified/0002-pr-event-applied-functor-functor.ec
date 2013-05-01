(* FIXME: disabled - this test is a non-sense

module type I = {
  fun init(b:bool): unit
  fun get(): bool
}.

module type J = {
  fun f() : bool
}.

module G(X:I) : J = {
  fun f(): bool = {
    var b:bool;
    X.init(true);
    b := X.get();
    return b;
  }
}.

op c:real.

axiom A: forall &m (M' <: I(M)), Pr[G(M').f() @ &m : res] = c.
*)
