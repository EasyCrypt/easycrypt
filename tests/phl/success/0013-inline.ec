(* -------------------------------------------------------------------- *)
require import Int.

module M = {
  proc f(x : int, y : int) : int = {
    var r : int = x + y;
    return r;
  }

  proc g(a : int) : int = {
    var z : int;

    z = f(a, a);
    return z;
  }
}.

(* -------------------------------------------------------------------- *)
lemma h1 : hoare[M.g : a = a ==> res = res].
proof.
  by proc; inline M.f; wp; skip; smt.
qed.

(* -------------------------------------------------------------------- *)
module type T = { proc f() : unit }.

module F(A:T) : T = {
  proc f() : unit = { A.f(); }
}.

hoare h2 (A <: T{M}) : F(A).f :true ==> true.
proof.
  proc; inline *.
  admit.
qed.
