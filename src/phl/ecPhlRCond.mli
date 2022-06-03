(* -------------------------------------------------------------------- *)
open EcSymbols
open EcParsetree
open EcCoreGoal.FApi

(* -------------------------------------------------------------------- *)
module Low : sig
  val t_hoare_rcond   : bool -> codepos1 -> backward
  val t_choare_rcond  : bool -> codepos1 -> EcFol.form option -> backward
  val t_bdhoare_rcond : bool -> codepos1 -> backward
  val t_equiv_rcond   : side -> bool -> codepos1 -> backward
end

(* -------------------------------------------------------------------- *)
module LowMatch : sig
  val t_hoare_rcond_match   : symbol -> codepos1 -> backward
  val t_bdhoare_rcond_match : symbol -> codepos1 -> backward
  val t_equiv_rcond_match   : side -> symbol -> codepos1 -> backward
end

(* -------------------------------------------------------------------- *)
val t_rcond       : oside -> bool -> codepos1 -> EcFol.form option -> backward
val process_rcond : oside -> bool -> codepos1 -> pformula option -> backward
val t_rcond_match : oside -> symbol -> codepos1 -> backward
