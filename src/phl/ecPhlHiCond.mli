(* -------------------------------------------------------------------- *)
open EcParsetree
open EcCoreGoal.FApi

(* -------------------------------------------------------------------- *)
val process_cond  : pcond_info -> backward
val process_match : matchmode -> backward
