(* -------------------------------------------------------------------- *)
open EcLocation
open EcParsetree
open EcBaseLogic
open EcLogic

(* -------------------------------------------------------------------- *)
class rn_hl_swap : bool option -> int -> int -> int ->
object
  inherit xrule

  method pos1 : int
  method pos2 : int
  method pos3 : int
  method side : bool option
end

(* -------------------------------------------------------------------- *)
val t_hoare_swap   : int -> int -> int -> tactic
val t_bdHoare_swap : int -> int -> int -> tactic
val t_equiv_swap   : bool -> int -> int -> int -> tactic

(* -------------------------------------------------------------------- *)
val process_swap : (bool option * swap_kind) located list -> tactic
