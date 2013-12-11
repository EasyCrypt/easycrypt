type t.

module type I = {
 proc f (x:t) : t 
}.

module type J = {
 proc g (x : t) : t 
}.

module M : I, J = {
  proc f(x:t) : t = { return x; }
  proc g(x:t) : t = { return x; }
}.
