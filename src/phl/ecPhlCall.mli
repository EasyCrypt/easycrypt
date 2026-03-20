(* -------------------------------------------------------------------- *)
open EcParsetree
open EcCoreGoal.FApi
open EcAst

(* -------------------------------------------------------------------- *)
val compute_hoare_call_post :
     EcEnv.LDecl.hyps
  -> EcMemory.memory
  -> form * exnpost
  -> lvalue option * EcPath.xpath * expr list
  -> exnpost
  -> form

(* -------------------------------------------------------------------- *)
val compute_equiv_call_post :
     EcEnv.LDecl.hyps
  -> EcMemory.memory * EcMemory.memory
  -> form * form
  -> ?mods:(EcPV.PV.t * EcPV.PV.t)
  -> EcModules.lvalue option * EcPath.xpath * EcTypes.expr list
  -> EcModules.lvalue option * EcPath.xpath * EcTypes.expr list
  -> form
  -> form

(* -------------------------------------------------------------------- *)
val compute_equiv1_call_post :
     EcEnv.LDecl.hyps
  -> side
  -> EcMemory.memory * EcMemory.memory
  -> form * form
  -> EcModules.lvalue option * EcPath.xpath * EcTypes.expr list
  -> form
  -> form
   
(* -------------------------------------------------------------------- *)
val t_hoare_call   : ss_inv -> hs_inv -> backward
val t_bdhoare_call : ss_inv -> ss_inv -> ss_inv option -> backward
val t_equiv_call   : ts_inv -> ts_inv -> backward
val t_equiv_call1  : side -> ss_inv -> ss_inv -> backward
val t_call         : oside -> form -> backward

(* -------------------------------------------------------------------- *)
val process_call : oside -> call_info gppterm -> backward

val process_call_concave : pformula * call_info gppterm -> backward
