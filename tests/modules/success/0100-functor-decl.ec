type t.

module type I = {
  proc f (x : t) : t
}.

module M(X : I) = {
  proc g (x:t) : t = { return x; }
}.
