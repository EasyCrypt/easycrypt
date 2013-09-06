(* -------------------------------------------------------------------- *)
open EcUtils
open EcPath
open EcParsetree
open EcFol
open EcBaseLogic
open EcLogic

(* -------------------------------------------------------------------- *)
class rn_hl_fel : form -> form -> form -> form -> (xpath * form) list ->
object
  inherit xrule

  method ash    : form
  method cntr   : form
  method fevent : form
  method preds  : (xpath * form) list
  method q      : form
end

(* -------------------------------------------------------------------- *)
val t_failure_event :
  int -> form -> form -> form -> form -> (xpath * form) list -> form -> tactic

(* -------------------------------------------------------------------- *)
type pfel_t =
    pformula
  * pformula
  * pformula
  * pformula
  * (pgamepath * pformula) list
  * pformula option

val process_fel : int -> pfel_t -> tactic
