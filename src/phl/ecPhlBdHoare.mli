(* -------------------------------------------------------------------- *)
open EcBaseLogic
open EcLogic

(* -------------------------------------------------------------------- *)
class rn_hl_hoare_bd_hoare : object inherit xrule end

val t_hoare_bd_hoare : tactic

(* -------------------------------------------------------------------- *)
class rn_bdhoare_split : object inherit xrule end

val process_bdhoare_split : EcParsetree.bdh_split -> tactic
