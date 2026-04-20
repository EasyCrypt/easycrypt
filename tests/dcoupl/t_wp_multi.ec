(* wp: handle multiple assignments in a chain. *)
require import AllCore Distr.

module M = {
  var a, b, c : int
  proc f() : int = {
    M.a <- 1;
    M.b <- 2;
    M.c <- 3;
    return M.c;
  }
  proc g() : int = {
    M.a <- 1;
    M.b <- 2;
    M.c <- 3;
    return M.c;
  }
}.

(* wp walks through all 3 assignments. *)
lemma wp_chain : equiv[ M.f ~ M.g : true ==> ={M.c} ].
proof.
proc. delay.
dcoupl wp.
dcoupl skip. smt().
qed.

(* One-sided wp. *)
lemma wp_one_sided : equiv[ M.f ~ M.g : true ==> true ].
proof.
proc. delay.
dcoupl wp {1}.
dcoupl wp {2}.
dcoupl skip. smt().
qed.
