(* Error paths: tactics must fail cleanly on wrong shapes. *)
require import AllCore Distr DBool.

module N = {
  var b : int
  proc h() : int = { N.b <- 1; return N.b; }
  proc k() : int = { N.b <- 1; return N.b; }
}.

(* skip fails when bodies non-empty. *)
lemma skip_fails_nonempty_body :
  equiv[ N.h ~ N.k : true ==> true ].
proof.
proc. delay.
fail dcoupl skip.   (* body = N.b <- 1 on both sides, skip requires empty *)
admit.
qed.

(* push with N exceeding body length. *)
lemma push_too_many :
  equiv[ N.h ~ N.k : true ==> true ].
proof.
proc. delay.
fail dcoupl push 5.
admit.
qed.

(* pop when R is empty. *)
lemma pop_empty_R :
  equiv[ N.h ~ N.k : true ==> true ].
proof.
proc. delay.
fail dcoupl pop 1.
admit.
qed.

(* undelay on dcoupl with non-empty R succeeds: R is prepended to the body. *)
lemma undelay_nonempty_R :
  equiv[ N.h ~ N.k : true ==> true ].
proof.
proc. delay.
dcoupl push 1.
undelay. auto.
qed.

(* undelay on dcoupl with non-empty S fails. *)
lemma undelay_nonempty_S :
  equiv[ N.h ~ N.k : true ==> true ].
proof.
proc. delay.
dcoupl seq 1 1 (true) with (N.b <- 1; ~ N.b <- 1;).
(* First goal has S_i = N.b <- 1. *)
fail undelay.
admit. admit.
qed.

(* asgn fails when the chosen-side body does not end in an assignment. *)
lemma asgn_fails_empty_body :
  equiv[ N.h ~ N.k : true ==> true ].
proof.
proc. delay.
dcoupl push 1.
fail dcoupl asgn {1}.
admit.
qed.
