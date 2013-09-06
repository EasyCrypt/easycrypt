(* -------------------------------------------------------------------- *)
open EcParsetree
open EcBaseLogic
open EcLogic

(* -------------------------------------------------------------------- *)
class rn_hl_inline : bool option -> s_pat ->
object
  inherit xrule

  method side    : bool option
  method pattern : s_pat
end

(* -------------------------------------------------------------------- *)
val t_inline_bdHoare : s_pat -> tactic
val t_inline_hoare   : s_pat -> tactic
val t_inline_equiv   : bool  -> s_pat -> tactic

(* -------------------------------------------------------------------- *)
val process_inline : pinline_arg -> tactic
