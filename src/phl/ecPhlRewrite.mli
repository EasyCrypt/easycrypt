(* -------------------------------------------------------------------- *)
open EcParsetree
open EcCoreGoal.FApi

(* -------------------------------------------------------------------- *)
val process_change : side option -> codepos -> pexpr -> backward

val process_rewrite_rw    : side option -> codepos -> ppterm -> backward
val process_rewrite_simpl : side option -> codepos -> backward
val process_rewrite       : side option -> codepos -> prrewrite -> backward
