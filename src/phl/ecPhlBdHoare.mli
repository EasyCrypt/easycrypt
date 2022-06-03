(* -------------------------------------------------------------------- *)
open EcFol
open EcCoreGoal.FApi

(* -------------------------------------------------------------------- *)
val t_bdhoare_and    : form -> form -> form -> backward
val t_bdhoare_or     : form -> form -> form -> backward
val t_bdhoare_not    : form -> form -> backward
val t_hoare_bd_hoare : backward
