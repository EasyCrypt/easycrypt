(* Reflexivity of a conditional procedure via dcoupl if. *)
require import AllCore Distr.

module M = {
  var a : int
  proc f() : int = {
    if (M.a = 0) { M.a <- 1; } else { M.a <- 2; }
    return M.a;
  }
}.

lemma refl_if : equiv[ M.f ~ M.f : ={M.a} ==> ={M.a} ].
proof.
proc. delay.
dcoupl if.
- smt().
- dcoupl wp. dcoupl skip. smt().
- dcoupl wp. dcoupl skip. smt().
qed.
