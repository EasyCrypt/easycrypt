(* -------------------------------------------------------------------- *)
open EcBaseLogic
open EcLogic

val t_hoare_bd_hoare : tactic

val process_bdhoare_split : EcParsetree.bdh_split -> tactic
