type t.

module type I = {
  fun f (x : t) : t
}.

module M(X : I) = {
  fun g (x:t) : t = { return x; }
}.
