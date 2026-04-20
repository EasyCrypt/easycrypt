(* seq: default T_i = R_i; C_i, and user-supplied T_i. *)
require import AllCore Distr.

module M = {
  var a : int
  proc f() : int = { M.a <- 1; M.a <- 2; return M.a; }
  proc g() : int = { M.a <- 1; M.a <- 2; return M.a; }
}.

(* seq with default T_i, then close both halves via wp + skip. *)
lemma seq_default : equiv[ M.f ~ M.g : ={M.a} ==> ={M.a} ].
proof.
proc. delay.
dcoupl seq 1 1 (={M.a}).
- (* First half: {={M.a} | eps x eps} a<-1 ~ a<-1 {={M.a} | a<-1 x a<-1} *)
  dcoupl push.    (* matches the Push axiom (theta = pre, S = R;C) *)
- (* Second half has non-empty R (from T default). Unpop to restore body. *)
  dcoupl unpop 1.
  dcoupl wp. dcoupl skip. smt().
qed.

(* seq with custom T_i = eps — avoids the non-empty R issue. *)
lemma seq_custom_T_empty :
  equiv[ M.f ~ M.g : ={M.a} ==> ={M.a} ].
proof.
proc. delay.
dcoupl seq 1 1 (={M.a}) with ( ~ ).
- (* First half: body a<-1 ~ a<-1, R=eps, S=eps (because T=eps). *)
  dcoupl wp. dcoupl skip. smt().
- (* Second half: body a<-2 ~ a<-2, R=eps, S=eps. *)
  dcoupl wp. dcoupl skip. smt().
qed.
