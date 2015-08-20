(* -------------------------------------------------------------------- *)
module type I = {}.

module F(X : I) = {
  proc f() : unit = {}
}.

module M(X : I) = {
  proc g() : unit = {
    var x;
    x <@ F(X).f();
  }
}.
