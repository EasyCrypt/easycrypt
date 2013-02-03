type t.
type u.

module type I = {
  var x : t
}.

module M : I = {
  var x : u
}.
