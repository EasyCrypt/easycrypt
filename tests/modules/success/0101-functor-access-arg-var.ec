type t.

module type I = {
  proc f() : t 
}.

module M(X : I) = {
  var y : t

  proc init() : unit = {
    y  = X.f();
  }
}.
