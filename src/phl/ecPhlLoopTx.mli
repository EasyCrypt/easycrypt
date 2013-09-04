(* -------------------------------------------------------------------- *)
open EcParsetree
open EcTypes
open EcBaseLogic
open EcLogic

(* -------------------------------------------------------------------- *)
class rn_hl_fission : bool option -> codepos -> int * (int * int) ->
object
  inherit xrule

  method side     : bool option
  method position : codepos
  method split    : int * (int * int)
end

type fission_t = bool option * codepos * (int * (int * int))

val t_fission : bool option -> codepos -> int * (int * int) -> tactic

val process_fission : fission_t -> tactic

(* -------------------------------------------------------------------- *)
class rn_hl_fusion : bool option -> codepos -> int * (int * int) ->
object
  inherit xrule

  method position : codepos
  method side     : bool option
  method split    : int * (int * int)
end

type fusion_t = bool option * codepos * (int * (int * int))

val t_fusion : bool option -> codepos -> int * (int * int) -> tactic

val process_fusion : fusion_t -> tactic

(* -------------------------------------------------------------------- *)
class rn_hl_unroll : bool option -> codepos ->
object
  inherit xrule

  method position : codepos
  method side     : bool option
end

type unroll_t = bool option * EcParsetree.codepos

val t_unroll : bool option -> codepos -> tactic

val process_unroll : unroll_t -> tactic

(* -------------------------------------------------------------------- *)
class rn_hl_splitwhile : expr -> bool option -> codepos ->
object
  inherit xrule

  method condition : expr
  method position  : codepos
  method side      : bool option
end

type splitwhile_t = pexpr * bool option * codepos

val t_splitwhile : expr -> bool option -> codepos -> tactic

val process_splitwhile : splitwhile_t -> tactic
