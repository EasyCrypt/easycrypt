(* -------------------------------------------------------------------- *)
open EcParsetree
open EcFol
open EcLogic
open EcBaseLogic

(* P(R)HL : consequence rule
 *
 *   {spre} ? {spost}     pre => spre     spost => post
 * ------------------------------------------------------
 *                      {pre} ? {post}
 *)

(* -------------------------------------------------------------------- *)
class rn_hl_conseq : object inherit xrule end
class rn_hl_notmod : object inherit xrule end

(* -------------------------------------------------------------------- *)
val t_equivF_conseq   : form -> form -> tactic
val t_equivS_conseq   : form -> form -> tactic
val t_hoareF_conseq   : form -> form -> tactic
val t_hoareS_conseq   : form -> form -> tactic
val t_bdHoareF_conseq : form -> form -> tactic
val t_bdHoareS_conseq : form -> form -> tactic

val t_conseq : form -> form -> tactic

val process_conseq : bool -> ccfpattern -> tactic
