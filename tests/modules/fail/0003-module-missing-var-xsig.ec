type t.

module I = {
  var x : t
}.

module J = {
  var y : t
}.

module M : I, J = {
  var x : t
}.
