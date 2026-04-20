(* Reflexivity of a while-loop procedure via dcoupl conseq + while. *)
require import AllCore Distr.

module M = {
  var a : int
  proc f() : int = {
    while (M.a < 10) { M.a <- M.a + 1; }
    return M.a;
  }
}.

lemma refl_loop : equiv[ M.f ~ M.f : ={M.a} ==> ={M.a} ].
proof.
proc. delay.
dcoupl conseq (={M.a}) (={M.a} /\ !(M.a{1} < 10)).
- smt().
- smt().
- dcoupl while.
  + smt().
  + dcoupl wp. dcoupl skip. smt().
qed.
