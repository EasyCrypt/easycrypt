type t.
type u.

op c : u.

module type I = {
  proc f() : t
}.

module M : I = {
  proc f() : u = {
    return c;
  }
}.
