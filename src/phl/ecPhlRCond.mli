(* -------------------------------------------------------------------- *)
open EcBaseLogic
open EcLogic

(* -------------------------------------------------------------------- *)
class rn_hl_rcond : bool option -> bool -> int ->
object
  inherit xrule

  method branch   : bool
  method position : int
  method side     : bool option
end

(* -------------------------------------------------------------------- *)
module Low : sig
  val t_hoare_rcond   : bool -> int -> tactic
  val t_bdHoare_rcond : bool -> int -> tactic
  val t_equiv_rcond   : bool -> bool -> int -> tactic
end

(* -------------------------------------------------------------------- *)
val t_rcond : bool option -> bool -> int -> tactic
