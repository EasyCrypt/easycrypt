(* -------------------------------------------------------------------- *)
open EcParsetree
open EcCoreGoal.FApi

(* -------------------------------------------------------------------- *)
val process_change : side option -> pcodepos -> pexpr -> backward
val process_rewrite : side option -> pcodepos -> ppterm -> backward
