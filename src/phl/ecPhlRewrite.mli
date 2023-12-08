(* -------------------------------------------------------------------- *)
open EcParsetree
open EcCoreGoal.FApi

(* -------------------------------------------------------------------- *)
val process_change : side option -> codepos -> pformula -> backward
val process_rewrite : side option -> codepos -> ppterm -> backward
