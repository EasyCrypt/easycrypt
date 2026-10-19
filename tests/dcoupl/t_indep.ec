(* indep (Congr): remove a common T-suffix from the bodies and from the
   continuations:
     { phi | R1 x R2 } C1 ~ C2 { psi | S1 x S2 }
     ------------------------------------------------------
     { phi | R1 x R2 } C1;T1 ~ C2;T2 { psi | S1;T1 x S2;T2 }          *)
require import AllCore Distr.

module M = {
  var a, b : int
  proc f() : int = { return M.a; }
  proc g() : int = { return M.a; }
  proc h() : int = { M.a <- 1; M.a <- 2; return M.a; }
  proc k() : int = { M.a <- 1; M.a <- 2; return M.a; }
}.

(* indep fires only on the right shape; verify the error path. *)
lemma indep_empty :
  equiv[ M.f ~ M.g : true ==> true ].
proof.
proc. delay.
fail dcoupl indep 1 1.  (* R/S are too short *)
admit.
qed.

(* Positive case: seq with T_i = a<-2 gives a first premise whose bodies
   and continuations share the suffix a<-2. *)
lemma indep_suffix :
  equiv[ M.h ~ M.k : ={M.a} ==> ={M.a} ].
proof.
proc. delay.
dcoupl seq 2 2 (={M.a}) with (M.a <- 2; ~ M.a <- 2;).
- (* {={M.a} | eps} a<-1;a<-2 ~ a<-1;a<-2 {={M.a} | a<-2 x a<-2} *)
  dcoupl indep 1 1.
  (* {={M.a} | eps} a<-1 ~ a<-1 {={M.a} | eps x eps} *)
  dcoupl asgn {1}. dcoupl asgn {2}. dcoupl skip. smt().
- (* {={M.a} | a<-2 x a<-2} eps ~ eps {={M.a} | eps x eps} *)
  dcoupl pop 1.
  dcoupl asgn {1}. dcoupl asgn {2}. dcoupl skip. smt().
qed.

(* Negative case: the suffixes differ. *)
lemma indep_mismatch :
  equiv[ M.h ~ M.k : ={M.a} ==> ={M.a} ].
proof.
proc. delay.
dcoupl seq 2 2 (={M.a}) with (M.a <- 1; ~ M.a <- 1;).
(* First goal: bodies end in a<-2 but continuations end in a<-1. *)
fail dcoupl indep 1 1.
admit. admit.
qed.
