(* delay / undelay: round-trip, and error paths. *)
require import AllCore Distr.

module M = {
  proc f() : int = { return 0; }
  proc g() : int = { return 0; }
}.

(* delay + undelay on an equivS goal round-trips to equivS. *)
lemma delay_undelay_idem : equiv[ M.f ~ M.g : true ==> true ].
proof.
proc. delay. undelay. auto.
qed.

(* F-level: delay+undelay on a dcoupl[...] surface form. *)
lemma dcoupl_delay_undelay :
  dcoupl[ , M.f , ~ , M.g , : true ==> true ].
proof.
undelay.   (* F-level form with empty R/S → equivF *)
proc. auto.
qed.
