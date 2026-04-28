open EcParsetree
open EcPath
open EcAst
open EcModules
open EcCoreGoal.FApi

val t_equivS_trans_eq : side -> stmt -> backward

val t_outline_stmt : side -> codepos1 -> codepos1 -> stmt -> backward
val t_outline_proc : side -> codepos1 -> codepos1 -> xpath -> lvalue option -> backward

val process_outline : outline_info -> backward
