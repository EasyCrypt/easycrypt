(* -------------------------------------------------------------------- *)
open EcParsetree
open EcCoreGoal
open EcAst

(* -------------------------------------------------------------------- *)
val t_bdep_solve : tcenv1 -> tcenv 

val t_bdep_simplify : tcenv1 -> tcenv

val t_extens : string option -> FApi.backward -> FApi.backward
