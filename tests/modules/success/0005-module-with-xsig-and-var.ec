type t.

module type I = {
 fun f (x:t) : t 
}.

module type J = {
 fun g (x : t) : t 
}.

module M : I, J = {
  fun f(x:t) : t = { return x; }
  fun g(x:t) : t = { return x; }
}.
