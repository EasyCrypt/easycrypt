(* symmetry: swap left <-> right. *)
require import AllCore Distr.

module M = {
  proc f() : int = { return 0; }
  proc g() : int = { return 0; }
}.

(* Sym composes with itself to identity (up to memenv swap). *)
lemma sym_sym_idem : equiv[ M.f ~ M.g : true ==> true ].
proof.
proc. delay.
dcoupl symmetry.
dcoupl symmetry.
dcoupl skip. smt().
qed.

(* After sym, close directly. *)
lemma sym_then_close : equiv[ M.f ~ M.g : true ==> true ].
proof.
proc. delay.
dcoupl symmetry.
dcoupl skip. smt().
qed.
