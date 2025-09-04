(* -------------------------------------------------------------------- *)
open EcParsetree
open EcCoreGoal.FApi
open EcAst

(* -------------------------------------------------------------------- *)
val wp2_call :
     EcEnv.env -> ts_inv -> ts_inv
  -> EcModules.lvalue option * EcPath.xpath * EcTypes.expr list
  -> EcPV.PV.t
  -> EcModules.lvalue option * EcPath.xpath * EcTypes.expr list
  -> EcPV.PV.t
  -> ts_inv
  -> EcEnv.LDecl.hyps -> ts_inv

val t_hoare_call   : ss_inv -> ss_inv -> backward
val t_bdhoare_call : ss_inv -> ss_inv -> ss_inv option -> backward
val t_equiv_call   : ts_inv -> ts_inv -> backward
val t_equiv_call1  : side -> ss_inv -> ss_inv -> backward
val t_call         : oside -> form -> backward

(* -------------------------------------------------------------------- *)
val process_call : oside -> call_info gppterm -> backward

val process_call_concave : pformula * call_info gppterm -> backward
