(* -------------------------------------------------------------------- *)
open EcParsetree
open EcBaseLogic
open EcLogic

(* -------------------------------------------------------------------- *)
class rn_hl_kill : bool option -> codepos -> int option ->
object
  inherit xrule

  method length   : int option
  method position : codepos
  method side     : bool option
end

val t_kill : bool option -> codepos -> int option -> tactic
val process_kill : bool option * codepos * int option -> tactic

(* -------------------------------------------------------------------- *)
class rn_hl_alias : bool option -> codepos ->
object
  inherit xrule

  method position : codepos
  method side     : bool option
end

val t_alias : bool option -> codepos -> psymbol option -> tactic
val process_alias : bool option * codepos * psymbol option -> tactic

(* -------------------------------------------------------------------- *)
class rn_hl_set : bool option -> codepos ->
object
  inherit xrule

  method position : codepos
  method side     : bool option
end

val t_set : bool -> bool option -> 
   codepos -> psymbol -> EcTypes.expr -> tactic
val process_set : 
  bool * bool option * codepos * psymbol * pexpr -> tactic

(* -------------------------------------------------------------------- *)
class rn_hl_cfold : bool option -> codepos -> int option ->
object
  inherit xrule

  method length   : int option
  method position : codepos
  method side     : bool option
end

val t_cfold : bool option -> codepos -> int option -> tactic
val process_cfold : bool option * codepos * int option -> tactic

