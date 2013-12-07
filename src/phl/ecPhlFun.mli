(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcTypes
open EcFol
open EcBaseLogic
open EcLogic

(* -------------------------------------------------------------------- *)
class rn_hl_fun_def : object
  inherit xrule
end

class rn_hl_fun_abs : form -> object
  inherit xrule

  method phi : form
end

class rn_hl_fun_code : object
  inherit xrule
end

class rn_hl_fun_upto : form -> form -> form -> object
  inherit xrule

  method bad  : form
  method inv1 : form
  method inv2 : form
end

(* TODO : move this ? *)
val check_concrete : EcEnv.env -> EcPath.xpath -> unit
(* -------------------------------------------------------------------- *)
module FunDefLow : sig
  val subst_pre : 
    EcEnv.env -> EcPath.xpath -> EcModules.funsig ->
    EcMemory.memory -> EcPV.PVM.subst -> EcPV.PVM.subst
  val t_hoareF_fun_def   : tactic
  val t_bdHoareF_fun_def : tactic
  val t_equivF_fun_def   : tactic
end

(* -------------------------------------------------------------------- *)
module FunAbsLow : sig
  val t_hoareF_abs   : form -> tactic
  val t_bdHoareF_abs : form -> tactic
  val equivF_abs_spec : EcEnv.env -> EcPath.xpath -> EcPath.xpath ->
    EcFol.form -> EcFol.form * EcFol.form * EcFol.form list
  val t_equivF_abs   : form -> tactic
end

(* -------------------------------------------------------------------- *)
module UpToLow : sig
  val t_equivF_abs_upto : form -> form -> form -> tactic
end

val t_fun_def : tactic
val t_fun : form -> tactic
val t_fun_to_code : tactic

(* -------------------------------------------------------------------- *)
val process_fun_abs : pformula -> tactic

type p_upto_info = pformula * pformula * (pformula option)

val process_fun_upto_info : p_upto_info -> goal -> form tuple3

val process_fun_upto : p_upto_info -> tactic
