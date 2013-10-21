(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcTypes
open EcFol
open EcBaseLogic
open EcLogic

(* -------------------------------------------------------------------- *)
class rn_hl_prbounded : object inherit xrule end
class rn_hl_prfalse   : object inherit xrule end

(* -------------------------------------------------------------------- *)
val t_ppr       : ty -> form -> form -> tactic
val t_prbounded : bool -> tactic
val t_prfalse   : tactic

(* -------------------------------------------------------------------- *)
val process_ppr : (pformula tuple2) option -> tactic
