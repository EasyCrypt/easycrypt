type t.

module type I = {
 proc f(x : t) : t 
}.

module M : I = {
 proc f(x:t) : t = { return x; }
}.
