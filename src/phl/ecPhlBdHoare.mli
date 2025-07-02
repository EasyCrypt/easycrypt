(* -------------------------------------------------------------------- *)
open EcCoreGoal.FApi
open EcAst

(* -------------------------------------------------------------------- *)
val t_bdhoare_and    : ss_inv -> ss_inv -> ss_inv -> backward
val t_bdhoare_or     : ss_inv -> ss_inv -> ss_inv -> backward
val t_bdhoare_not    : ss_inv -> ss_inv -> backward
val t_hoare_bd_hoare : backward
