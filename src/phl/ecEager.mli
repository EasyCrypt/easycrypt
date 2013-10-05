open EcBaseLogic
open EcFol
open EcLogic
open EcParsetree

(* -------------------------------------------------------------------- *)
class rn_eager_seq : object
  inherit xrule 
end

val t_eager_seq : int -> int -> form -> EcIdent.t -> tactic
val process_seq : 
  eager_info -> int * int -> pformula -> tactic


(* -------------------------------------------------------------------- *)
val t_eager_if : tactic
val process_if : tactic

(* -------------------------------------------------------------------- *)
class rn_eager_while : object
  inherit xrule 
end

val t_eager_while : EcIdent.t -> tactic
val process_while : eager_info -> tactic

(* -------------------------------------------------------------------- *)
class rn_eager_fun_def : object
  inherit xrule 
end

val t_eager_fun_def : tactic
val process_fun_def : tactic

class rn_eager_fun_abs : object
  inherit xrule 
end

val t_eager_fun_abs : EcFol.form -> EcIdent.t -> EcLogic.goal -> EcLogic.goals
val process_fun_abs : 
  eager_info -> pformula -> EcLogic.goal -> EcLogic.goals

(* -------------------------------------------------------------------- *)
class rn_eager_call :
object
  inherit xrule 
end

val t_eager_call : form -> form -> tactic
val process_call : call_info fpattern -> tactic

(* -------------------------------------------------------------------- *)
val process_eager : eager_info -> pformula -> tactic
