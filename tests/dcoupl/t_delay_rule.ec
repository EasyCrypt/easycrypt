(* Delay rule: closes { phi | R x R' } C ~ C' { psi | R;C x R';C' } with the
   single subgoal phi => psi. The natural way to reach the shape is via
   seq with an explicit intermediate context T_i = R_i; C_i.          *)
require import AllCore Distr.

module M = {
  var a : int
  proc f() : int = { M.a <- 1; M.a <- 2; return M.a; }
  proc g() : int = { M.a <- 1; M.a <- 2; return M.a; }
}.

(* After seq with T_i = R_i; C_i, premise 1 has exactly the Delay shape. *)
lemma delay_via_seq :
  equiv[ M.f ~ M.g : ={M.a} ==> ={M.a} ].
proof.
proc. delay.
dcoupl seq 1 1 (={M.a}) with (M.a <- 1; ~ M.a <- 1;).
- dcoupl delay. smt().
- dcoupl pop 1.
  dcoupl asgn {1}. dcoupl asgn {1}.
  dcoupl asgn {2}. dcoupl asgn {2}.
  dcoupl skip. smt().
qed.

(* One-sided Delay: the other-side body must be empty and its
   continuation must equal its delay context. *)
lemma delay_left_via_seq :
  equiv[ M.f ~ M.g : ={M.a} ==> ={M.a} ].
proof.
proc. delay.
dcoupl seq 1 0 (={M.a}) with (M.a <- 1; ~ ).
- dcoupl delay {1}. smt().
- dcoupl pop {1} 1.
  dcoupl asgn {1}. dcoupl asgn {1}.
  dcoupl asgn {2}. dcoupl asgn {2}.
  dcoupl skip. smt().
qed.

(* Delay fails when the continuations are not R_i; C_i. *)
lemma delay_bad_shape :
  equiv[ M.f ~ M.g : ={M.a} ==> ={M.a} ].
proof.
proc. delay.
fail dcoupl delay.
admit.
qed.
