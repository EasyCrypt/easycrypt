(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcTypes
open EcFol
open EcBaseLogic
open EcLogic

(* -------------------------------------------------------------------- *)
val t_ppr : ty -> form -> form -> tactic

(* -------------------------------------------------------------------- *)
val process_ppr : pformula tuple2 -> tactic
