(* -------------------------------------------------------------------- *)
open EcParsetree
open EcCoreGoal.FApi

(* -------------------------------------------------------------------- *)
val process_rewrite_rw    : side option -> pcodepos_or_range option -> ppterm -> backward
val process_rewrite_simpl : side option -> pcodepos_or_range option -> backward
val process_rewrite       : side option -> pcodepos_or_range option -> prrewrite -> backward
val process_rewrite_at    : psymbol -> ppterm -> backward
val process_change_stmt   : side option -> ptybindings option -> prange1_or_insert -> pstmt -> backward
