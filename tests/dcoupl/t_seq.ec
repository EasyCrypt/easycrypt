(* seq: default T_i = R_i, and user-supplied T_i. *)
require import AllCore Distr.

module M = {
  var a : int
  proc f() : int = { M.a <- 1; M.a <- 2; return M.a; }
  proc g() : int = { M.a <- 1; M.a <- 2; return M.a; }
}.

(* seq with default T_i (= R_i = eps), then close both halves via
   asgn + skip. *)
lemma seq_default : equiv[ M.f ~ M.g : ={M.a} ==> ={M.a} ].
proof.
proc. delay.
dcoupl seq 1 1 (={M.a}).
- (* First half: {={M.a} | eps x eps} a<-1 ~ a<-1 {={M.a} | eps x eps} *)
  dcoupl asgn {1}. dcoupl asgn {2}. dcoupl skip. smt().
- (* Second half: {={M.a} | eps x eps} a<-2 ~ a<-2 {={M.a} | eps x eps} *)
  dcoupl asgn {1}. dcoupl asgn {2}. dcoupl skip. smt().
qed.

(* seq with explicit empty T_i. *)
lemma seq_custom_T_empty :
  equiv[ M.f ~ M.g : ={M.a} ==> ={M.a} ].
proof.
proc. delay.
dcoupl seq 1 1 (={M.a}) with ( ~ ).
- dcoupl asgn {1}. dcoupl asgn {2}. dcoupl skip. smt().
- dcoupl asgn {1}. dcoupl asgn {2}. dcoupl skip. smt().
qed.

(* seq with T_i referring to the current contexts by name: [r] stands
   for R_i and [s] for S_i inside the supplied statements. *)
lemma seq_custom_T_named :
  equiv[ M.f ~ M.g : ={M.a} ==> ={M.a} ].
proof.
proc. delay.
dcoupl push 1.
(* R_i = a<-1, body = a<-2 on both sides. *)
dcoupl seq 1 1 (={M.a}) with (r; M.a <- 2; ~ r; M.a <- 2;).
- (* {={M.a} | a<-1 x a<-1} a<-2 ~ a<-2 {={M.a} | a<-1;a<-2 x a<-1;a<-2} *)
  dcoupl delay. smt().
- (* {={M.a} | a<-1;a<-2 x ...} eps ~ eps {={M.a} | eps x eps} *)
  dcoupl pop 2.
  dcoupl asgn {1}. dcoupl asgn {1}.
  dcoupl asgn {2}. dcoupl asgn {2}.
  dcoupl skip. smt().
qed.
