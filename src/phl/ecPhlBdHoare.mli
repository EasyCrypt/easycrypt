(* -------------------------------------------------------------------- *)
open EcTypes
open EcFol
open EcBaseLogic
open EcLogic

(* -------------------------------------------------------------------- *)
class rn_hl_hoare_equiv    : object inherit xrule end
class rn_hl_hoare_bd_hoare : object inherit xrule end
class rn_hoare_true        : object inherit xrule end

val t_hoare_equiv    : form -> form -> form -> form -> form -> form -> tactic
val t_hoare_bd_hoare : tactic
val t_bdeq           : tactic
val t_hoare_true     : tactic
