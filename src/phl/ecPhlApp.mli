(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcFol
open EcBaseLogic
open EcLogic

(* -------------------------------------------------------------------- *)
class rn_hl_append : tac_dir -> int doption -> form -> app_bd_info ->
object
  inherit xrule

  method bdi     : app_bd_info
  method doption : int doption
  method phi     : form
  method tacdir  : tac_dir
end

(* ------------------------------------------------------------------------------- *)
val t_hoare_app   : int -> form -> tactic
val t_bdHoare_app : int -> form tuple6 -> tactic
val t_equiv_app   : int * int -> form -> tactic

(* -------------------------------------------------------------------- *)
val process_app :
  tac_dir -> int doption -> pformula -> p_app_bd_info -> tactic
