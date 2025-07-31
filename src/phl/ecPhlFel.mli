(* -------------------------------------------------------------------- *)
open EcPath
open EcParsetree
open EcFol
open EcAst
open EcCoreGoal.FApi
open EcMatching.Position

(* -------------------------------------------------------------------- *)
val t_failure_event :
     EcMemory.memory
  -> codepos1
  -> form -> form -> form -> form
  -> (xpath * ss_inv) list
  -> form
  -> backward

(* -------------------------------------------------------------------- *)
val process_fel : pcodepos1 -> fel_info -> backward
