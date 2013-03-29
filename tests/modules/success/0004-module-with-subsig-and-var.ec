type t.

module type I = {
 fun f(x : t) : t 
}.

module M : I = {
  var y : t
  fun f (x : t) : t = { return t; }
}.
