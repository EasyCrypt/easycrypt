(* pop / unpop: round-trip, one-sided, multi-instruction. *)
require import AllCore Distr.

module M = {
  var a : int
  proc f() : int = { M.a <- 0; M.a <- 1; M.a <- 2; return M.a; }
  proc g() : int = { M.a <- 0; M.a <- 1; M.a <- 2; return M.a; }
}.

(* Two-sided pop N then unpop N is identity. *)
lemma pop_unpop_roundtrip : equiv[ M.f ~ M.g : true ==> true ].
proof.
proc. delay.
dcoupl pop 3.
dcoupl unpop 3.
undelay. auto.
qed.

(* One-sided pop + unpop. *)
lemma pop_l_unpop_l : equiv[ M.f ~ M.g : true ==> true ].
proof.
proc. delay.
dcoupl pop {1} 2.
dcoupl unpop {1} 2.
undelay. auto.
qed.

lemma pop_r_unpop_r : equiv[ M.f ~ M.g : true ==> true ].
proof.
proc. delay.
dcoupl pop {2} 2.
dcoupl unpop {2} 2.
undelay. auto.
qed.

(* Pop consumed entire body, then unpop restores. *)
lemma pop_full_roundtrip : equiv[ M.f ~ M.g : true ==> true ].
proof.
proc. delay.
dcoupl pop 3.     (* body becomes empty, R has 3 instrs *)
dcoupl unpop 3.   (* body has 3 instrs again, R empty *)
undelay. auto.
qed.
