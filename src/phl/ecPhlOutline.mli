open EcCoreGoal.FApi
open EcParsetree
open EcModules
open EcPath

val t_equivS_trans_eq : side -> stmt -> backward

val t_outline_stmt : side -> codepos1 -> codepos1 -> stmt -> backward
val t_outline_proc : side -> codepos1 -> codepos1 -> xpath -> lvalue option -> backward

val process_outline : outline_info -> backward
