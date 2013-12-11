type t.

module type I = {
 proc f(x : t) : t 
}.

module M : I = {
  var y : t

  proc f (x : t) : t = {
    return x;
  }
}.
