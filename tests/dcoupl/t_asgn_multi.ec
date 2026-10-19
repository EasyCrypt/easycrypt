(* asgn: handle multiple assignments in a chain, one side at a time.
   Each application consumes the last assignment of the chosen body. *)
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

(* asgn walks through all 3 assignments on each side. *)
lemma asgn_chain : equiv[ M.f ~ M.g : true ==> ={M.c} ].
proof.
proc. delay.
dcoupl asgn {1}. dcoupl asgn {1}. dcoupl asgn {1}.
dcoupl asgn {2}. dcoupl asgn {2}. dcoupl asgn {2}.
dcoupl skip. smt().
qed.

(* Interleaving sides is allowed. *)
lemma asgn_interleaved : equiv[ M.f ~ M.g : true ==> ={M.a, M.b, M.c} ].
proof.
proc. delay.
do 3! (dcoupl asgn {1}; dcoupl asgn {2}).
dcoupl skip. smt().
qed.

(* asgn substitutes the assigned value into the continuation S_side. *)
lemma asgn_into_S : equiv[ M.f ~ M.g : true ==> ={M.c} ].
proof.
proc. delay.
dcoupl seq 2 2 (={M.b}) with (M.c <- M.b + 1; ~ M.c <- M.b + 1;).
- (* S_i = c <- b + 1; consuming b <- 2 rewrites it to c <- 2 + 1. *)
  dcoupl asgn {1}. dcoupl asgn {1}.
  dcoupl asgn {2}. dcoupl asgn {2}.
  admit.
- admit.
qed.
