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

(* pop with N exceeding body length. *)
lemma pop_too_many :
  equiv[ N.h ~ N.k : true ==> true ].
proof.
proc. delay.
fail dcoupl pop 5.
admit.
qed.

(* unpop when R is empty. *)
lemma unpop_empty_R :
  equiv[ N.h ~ N.k : true ==> true ].
proof.
proc. delay.
fail dcoupl unpop 1.
admit.
qed.

(* undelay on dcoupl with non-empty R fails. *)
lemma undelay_nonempty_R :
  equiv[ N.h ~ N.k : true ==> true ].
proof.
proc. delay.
dcoupl pop 1.
fail undelay.
admit.
qed.
