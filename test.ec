op foo : 'a -> bool.

axiom foo_int  : forall (x : int ), foo(x) = true.
axiom foo_bool : forall (x : bool), foo(x) = false.
