(* -------------------------------------------------------------------- *)
open EcSymbols
open EcParsetree
open EcCoreGoal.FApi
open EcMatching.Position

(* -------------------------------------------------------------------- *)
module Low : sig
  val t_hoare_rcond   : bool -> codepos1 -> backward
  val t_ehoare_rcond  : bool -> codepos1 -> backward
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
val t_rcond       : oside -> bool -> codepos1 -> backward
val process_rcond : oside -> bool -> pcodepos1 -> backward

(* -------------------------------------------------------------------- *)
val process_rcond_match : oside -> symbol -> pcodepos1 -> backward
val t_rcond_match       : oside -> symbol -> codepos1 -> backward
