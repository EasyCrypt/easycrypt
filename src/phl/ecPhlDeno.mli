(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcFol
open EcBaseLogic
open EcLogic

(* -------------------------------------------------------------------- *)
class rn_hl_deno : object
  inherit xrule
end

(* -------------------------------------------------------------------- *)
val t_bdHoare_deno : form -> form -> tactic
val t_equiv_deno   : form -> form -> tactic

(* -------------------------------------------------------------------- *)
val process_bdHoare_deno : ((pformula option) tuple2) fpattern -> tactic
val process_equiv_deno   : ((pformula option) tuple2) fpattern -> tactic
