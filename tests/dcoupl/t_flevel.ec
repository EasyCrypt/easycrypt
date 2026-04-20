(* F-level surface syntax: dcoupl[...] + proc + close. *)
require import AllCore Distr.

module M = {
  var a : int
  proc f() : int = { M.a <- 1; return M.a; }
  proc g() : int = { M.a <- 1; return M.a; }
}.

(* Full proof path starting from the F-level dcoupl[...] surface with
   empty R/S. *)
lemma dcoupl_surface_empty_ctx :
  dcoupl[ , M.f , ~ , M.g , : ={M.a} ==> ={M.a} ].
proof.
proc.
dcoupl wp.
dcoupl skip.
smt().
qed.

(* Empty contexts, trivial postcondition. *)
lemma dcoupl_surface_true :
  dcoupl[ , M.f , ~ , M.g , : true ==> true ].
proof.
proc.
dcoupl wp.
dcoupl skip.
smt().
qed.
