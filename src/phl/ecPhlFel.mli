(* -------------------------------------------------------------------- *)
open EcPath
open EcParsetree
open EcAst
open EcCoreGoal.FApi
open EcMatching.Position

(* -------------------------------------------------------------------- *)
val t_failure_event :
     codepos1
  -> ss_inv -> form -> form -> ss_inv
  -> (xpath * ss_inv) list
  -> ss_inv
  -> backward

(* -------------------------------------------------------------------- *)
val process_fel : pcodepos1 -> fel_info -> backward
