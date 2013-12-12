(* -------------------------------------------------------------------- *)
open EcSymbols
open EcBaseLogic
open EcLogic

(* -------------------------------------------------------------------- *)
class rn_hl_pr_lemma :
object
  inherit xrule
end

(* -------------------------------------------------------------------- *)
val t_pr_rewrite : symbol -> tactic

