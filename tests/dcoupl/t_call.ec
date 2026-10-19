(* call: concrete procedures, two-sided (with an F-level dcoupl spec)
   and one-sided (with a lossless hoare spec). Stacks handed over to
   a callee must only mention global variables.                       *)
require import AllCore Distr.

module M = {
  var a, b : int
  proc h(x : int) : int = { M.a <- x + 1; return M.a; }
  proc k(x : int) : int = { M.a <- x + 1; return M.a; }

  proc f() : int = { var r : int; r <@ h(1); return r; }
  proc g() : int = { var r : int; r <@ k(1); return r; }

  (* a delayed global assignment around the call *)
  proc fb() : int = { var r : int; M.b <- 5; r <@ h(1); return r + M.b; }
  proc gb() : int = { var r : int; M.b <- 5; r <@ k(1); return r + M.b; }

  (* argument reading a global *)
  proc fa() : int = { var r : int; r <@ h(M.a); return r; }

  (* local used around the call *)
  proc fl() : int = { var r : int; r <- 0; r <@ h(r); return r; }

  (* result into a global, then overwritten *)
  proc fr() : int = { M.a <@ h(1); M.a <- 0; return M.a; }

  proc ga() : int = { M.a <- 2; return M.a; }
}.

(* Two-sided call with a cut specification; empty stacks. *)
lemma call_cut : equiv[ M.f ~ M.g : true ==> ={res} ].
proof.
proc. delay.
dcoupl call (_: ={x} ==> ={res}).
- (* dcoupl[ , M.h, ~ , M.k, : ={x} ==> ={res} ] *)
  proc. dcoupl asgn {1}. dcoupl asgn {2}. dcoupl skip. smt().
- dcoupl skip. smt().
qed.

(* Two-sided call with a lemma. *)
lemma hk : dcoupl[ , M.h , ~ , M.k , : ={x} ==> ={res} ].
proof.
proc. dcoupl asgn {1}. dcoupl asgn {2}. dcoupl skip. smt().
qed.

lemma call_lemma : equiv[ M.f ~ M.g : true ==> ={res} ].
proof.
proc. delay.
dcoupl call hk.
dcoupl skip. smt().
qed.

(* A delayed global assignment is pushed through the call: the stacks
   T_i = (M.b <- 5) become the delay contexts of the specification,
   whose continuations are empty like the goal's. The post must then
   say something about M.b, which T_i writes.                         *)
lemma call_through_stacks : equiv[ M.fb ~ M.gb : true ==> ={res} ].
proof.
proc. delay.
dcoupl push 1.
dcoupl call (_: ={x} ==> ={res, M.b}) with (M.b <- 5; ~ M.b <- 5;).
- (* dcoupl[ M.b <- 5, M.h, ~ M.b <- 5, M.k, : ={x} ==> ={res, M.b} ] *)
  proc. dcoupl pop 1.
  dcoupl asgn {1}. dcoupl asgn {1}. dcoupl asgn {2}. dcoupl asgn {2}.
  dcoupl skip. smt().
- dcoupl skip. smt().
qed.

(* The same with the named stacks [r] (the current delay contexts). *)
lemma call_through_stacks_named : equiv[ M.fb ~ M.gb : true ==> ={res} ].
proof.
proc. delay.
dcoupl push 1.
dcoupl call (_: ={x} ==> ={res, M.b}) with (r; ~ r;).
- proc. dcoupl pop 1.
  dcoupl asgn {1}. dcoupl asgn {1}. dcoupl asgn {2}. dcoupl asgn {2}.
  dcoupl skip. smt().
- dcoupl skip. smt().
qed.

(* The wp generalizes over the variables written by the stacks: a spec
   that is silent on M.b leaves an unprovable goal. *)
lemma call_through_stacks_weak : equiv[ M.fb ~ M.gb : true ==> ={res} ].
proof.
proc. delay.
dcoupl push 1.
dcoupl call (_: ={x} ==> ={res}) with (M.b <- 5; ~ M.b <- 5;).
- proc. dcoupl pop 1.
  dcoupl asgn {1}. dcoupl asgn {1}. dcoupl asgn {2}. dcoupl asgn {2}.
  dcoupl skip. smt().
- dcoupl skip.
  (* forall &1 &2, true => ... forall b_L b_R res_L res_R, res_L = res_R => res_L + b_L = res_R + b_R *)
  admit.
qed.

(* Error: stacks mentioning a caller local. *)
lemma call_local_stack : equiv[ M.fl ~ M.fl : true ==> ={res} ].
proof.
proc. delay.
dcoupl push 1.
fail dcoupl call (_: ={x} ==> ={res}) with (r <- 0; ~ r <- 0;).
admit.
qed.

(* Error: the arguments read a variable written by the stacks. *)
lemma call_args_vs_stack : equiv[ M.fa ~ M.fa : true ==> ={res} ].
proof.
proc. delay.
fail dcoupl call (_: ={x} ==> ={res}) with (M.a <- 0; ~ M.a <- 0;).
admit.
qed.

(* Error: the result variable is written by the continuation. *)
lemma call_res_vs_cont : equiv[ M.fr ~ M.fr : true ==> ={res} ].
proof.
proc. delay.
dcoupl seq 1 1 (true) with (M.a <- 0; ~ M.a <- 0;).
fail dcoupl call (_: true ==> true).
admit. admit.
qed.

(* One-sided call with a lossless hoare spec. *)
lemma call_left : equiv[ M.f ~ M.ga : true ==> ={res} ].
proof.
proc. delay.
dcoupl call{1} (_: x = 1 ==> res = 2).
- (* phoare[ M.h : x = 1 ==> res = 2 ] = 1%r *)
  proc. auto.
- dcoupl asgn {2}. dcoupl skip. smt().
qed.

(* One-sided call through an independent delayed instruction: S = R
   on the chosen side and the callee neither reads nor writes M.b.   *)
lemma call_left_stacks : equiv[ M.fb ~ M.ga : true ==> ={res} ].
proof.
proc. delay.
dcoupl seq 2 0 (true) with (M.b <- 5; ~ ).
- (* {true | eps} M.b <- 5; r <@ h(1) ~ eps {true | M.b <- 5 x eps} *)
  dcoupl push {1} 1.
  dcoupl call{1} (_: true ==> true).
  + proc. auto.
  + dcoupl skip. smt().
- (* {true | M.b <- 5 x eps} eps ~ M.a <- 2 {={res} | eps x eps} *)
  admit.
qed.

(* Error: one-sided call with a stack the callee writes. *)
lemma call_left_dep : equiv[ M.fa ~ M.ga : true ==> ={res} ].
proof.
proc. delay.
dcoupl seq 1 0 (true) with (M.a <- 0; ~ ).
dcoupl push {1} 1.
fail dcoupl call{1} (_: true ==> true).
admit. admit.
qed.
