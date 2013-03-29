type t.

module type I = {
 fun f(x : t) : t 
}.

module M : I = {
 fun f(x:t) : t = { return x; }
}.
