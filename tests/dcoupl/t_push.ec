(* Push axiom: closes { phi | R x R } C ~ C { phi | R;C x R;C }.
   The natural way to reach the shape is via seq (default T_i = R_i; C_i). *)
require import AllCore Distr.

module M = {
  var a : int
  proc f() : int = { M.a <- 1; M.a <- 2; return M.a; }
  proc g() : int = { M.a <- 1; M.a <- 2; return M.a; }
}.

(* After seq, premise 1 has exactly the Push axiom shape. *)
lemma push_via_seq :
  equiv[ M.f ~ M.g : ={M.a} ==> ={M.a} ].
proof.
proc. delay.
dcoupl seq 1 1 (={M.a}).
- dcoupl push.        (* closes axiom shape *)
- dcoupl unpop 1.
  dcoupl wp. dcoupl skip. smt().
qed.
