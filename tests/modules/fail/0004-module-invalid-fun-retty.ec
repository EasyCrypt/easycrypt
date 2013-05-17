type t.
type u.

op c : u.

module type I = {
  fun f() : t
}.

module M : I = {
  fun f() : u = {
    return c;
  }
}.
