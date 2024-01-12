(* -------------------------------------------------------------------- *)
open EcParsetree
open EcCoreGoal.FApi

(* -------------------------------------------------------------------- *)
val process_change : side option -> pcodepos -> pexpr -> backward

val process_rewrite_rw    : side option -> pcodepos -> ppterm -> backward
val process_rewrite_simpl : side option -> pcodepos -> backward
val process_rewrite       : side option -> pcodepos -> prrewrite -> backward
