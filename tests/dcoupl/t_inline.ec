(* inline on dcoupl goals: only the chosen body is unfolded, the delay
   and continuation stacks are left untouched (CallP of the paper). *)
require import AllCore Distr.

module M = {
  var a : int
  proc h(x : int) : int = { M.a <- x + 1; return M.a; }
  proc f() : int = { var r : int; r <@ h(1); return r; }
  proc g() : int = { M.a <- 2; return M.a; }
}.

(* Two-sided inline, then close with asgn/skip. *)
lemma inline_both : equiv[ M.f ~ M.f : true ==> ={res} ].
proof.
proc. delay.
inline M.h.
dcoupl asgn {1}. dcoupl asgn {1}. dcoupl asgn {1}.
dcoupl asgn {2}. dcoupl asgn {2}. dcoupl asgn {2}.
dcoupl skip. smt().
qed.

(* One-sided inline against a procedure without calls. *)
lemma inline_left : equiv[ M.f ~ M.g : true ==> ={res} ].
proof.
proc. delay.
inline{1} M.h.
dcoupl asgn {1}. dcoupl asgn {1}. dcoupl asgn {1}.
dcoupl asgn {2}.
dcoupl skip. smt().
qed.

(* inline * and inline with a code position. *)
lemma inline_star : equiv[ M.f ~ M.f : true ==> ={res} ].
proof.
proc. delay.
inline *.
do 3! (dcoupl asgn {1}; dcoupl asgn {2}).
dcoupl skip. smt().
qed.

(* The stacks are not inlined: a pushed call stays a call. *)
lemma inline_keeps_stacks : equiv[ M.f ~ M.f : true ==> ={res} ].
proof.
proc. delay.
dcoupl push 1.
inline M.h.    (* nothing to inline in the (empty) bodies *)
dcoupl pop 1.
inline M.h.
do 3! (dcoupl asgn {1}; dcoupl asgn {2}).
dcoupl skip. smt().
qed.
