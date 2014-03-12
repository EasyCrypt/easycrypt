(* -------------------------------------------------------------------- *)
open EcCoreGoal.FApi

(* -------------------------------------------------------------------- *)
val t_hoare_bd_hoare : backward
val process_bdhoare_split : EcParsetree.bdh_split -> backward
