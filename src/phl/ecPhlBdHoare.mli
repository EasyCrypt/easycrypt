(* -------------------------------------------------------------------- *)
open EcTypes
open EcFol
open EcBaseLogic
open EcLogic

(* -------------------------------------------------------------------- *)
class rn_hl_hoare_bd_hoare : object inherit xrule end

val t_hoare_bd_hoare : tactic
val t_bdeq           : tactic
