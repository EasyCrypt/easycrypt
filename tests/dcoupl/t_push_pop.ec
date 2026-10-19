(* push / pop: round-trip, one-sided, multi-instruction.
   push N moves the first N body instructions into R;
   pop N moves the last N instructions of R back to the front of the body. *)
require import AllCore Distr.

module M = {
  var a : int
  proc f() : int = { M.a <- 0; M.a <- 1; M.a <- 2; return M.a; }
  proc g() : int = { M.a <- 0; M.a <- 1; M.a <- 2; return M.a; }
}.

(* Two-sided push N then pop N is identity. *)
lemma push_pop_roundtrip : equiv[ M.f ~ M.g : true ==> true ].
proof.
proc. delay.
dcoupl push 3.
dcoupl pop 3.
undelay. auto.
qed.

(* One-sided push + pop. *)
lemma push_l_pop_l : equiv[ M.f ~ M.g : true ==> true ].
proof.
proc. delay.
dcoupl push {1} 2.
dcoupl pop {1} 2.
undelay. auto.
qed.

lemma push_r_pop_r : equiv[ M.f ~ M.g : true ==> true ].
proof.
proc. delay.
dcoupl push {2} 2.
dcoupl pop {2} 2.
undelay. auto.
qed.

(* Default count is 1. *)
lemma push_pop_default : equiv[ M.f ~ M.g : true ==> true ].
proof.
proc. delay.
dcoupl push.
dcoupl push {1}.
dcoupl pop {1}.
dcoupl pop.
undelay. auto.
qed.

(* Push consumed entire body, then pop restores. *)
lemma push_full_roundtrip : equiv[ M.f ~ M.g : true ==> true ].
proof.
proc. delay.
dcoupl push 3.    (* body becomes empty, R has 3 instrs *)
dcoupl pop 3.     (* body has 3 instrs again, R empty *)
undelay. auto.
qed.

(* Pushing a prefix then closing: the pushed instructions stay in R,
   so the leftover body is closed with asgn/skip after popping. *)
lemma push_then_close : equiv[ M.f ~ M.g : ={M.a} ==> ={M.a} ].
proof.
proc. delay.
dcoupl push 2.
dcoupl pop 2.
dcoupl asgn {1}. dcoupl asgn {1}. dcoupl asgn {1}.
dcoupl asgn {2}. dcoupl asgn {2}. dcoupl asgn {2}.
dcoupl skip. smt().
qed.
