open EcCoreGoal.FApi
open EcMatching.Position
open EcParsetree
open EcModules
open EcPath

val t_outline_stmt : side -> codepos1 -> codepos1 -> stmt -> backward
  val t_outline_proc : [`Exact | `Alias] -> side -> codepos1 -> codepos1 -> xpath -> backward

val process_outline : outline_info -> backward
