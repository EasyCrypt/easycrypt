type t.

module type I = {
  fun f() : t 
}.

module M(X : I) = {
  var y : t

  fun init() : unit = {
    y  = X.f();
  }
}.
