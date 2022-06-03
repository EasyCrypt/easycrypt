(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcPath
open EcFol
open EcModules
open EcMemory
open EcCoreGoal

(* -------------------------------------------------------------------- *)
(* FIXME: MOVE THIS! *)
val check_concrete : proofenv -> EcEnv.env -> EcPath.xpath -> unit

val subst_pre :
     EcEnv.env -> funsig -> memory
  -> EcPV.PVM.subst
  -> EcPV.PVM.subst

(* -------------------------------------------------------------------- *)
type p_upto_info = pformula * pformula * (pformula option)

type abs_inv_inf = (EcPath.xpath * EcParsetree.ptybinding * EcFol.cost) list

val process_p_abs_inv_inf :
  EcCoreGoal.tcenv1 ->
  EcEnv.LDecl.hyps ->
  p_abs_inv_inf ->
  abs_inv_inf

val process_inv_pabs_inv_finfo:
  EcCoreGoal.tcenv1 ->
  pformula ->
  p_abs_inv_inf ->
  form * abs_inv_inf

type inv_inf =  [
  | `Std     of cost
  | `CostAbs of abs_inv_inf
]

val process_fun_def       : FApi.backward
val process_fun_abs       : pformula -> p_abs_inv_inf option -> FApi.backward
val process_fun_upto_info : p_upto_info -> tcenv1 -> form tuple3
val process_fun_upto      : p_upto_info -> FApi.backward
val process_fun_to_code   : FApi.backward

(* -------------------------------------------------------------------- *)
module FunAbsLow : sig
  val hoareF_abs_spec :
       proofenv -> EcEnv.env -> xpath -> form
    -> form * form * form list

  val choareF_abs_spec :
       proofenv -> EcEnv.env -> xpath -> form -> abs_inv_inf
    -> form * form * cost * form list

  val bdhoareF_abs_spec :
       proofenv -> EcEnv.env -> xpath -> form
    -> form * form * form list

  val equivF_abs_spec :
       proofenv -> EcEnv.env -> xpath -> xpath -> form
    -> form * form * form list
end

(* -------------------------------------------------------------------- *)
val t_hoareF_abs   : form -> FApi.backward
val t_choareF_abs  : form -> abs_inv_inf -> FApi.backward
val t_bdhoareF_abs : form -> FApi.backward
val t_equivF_abs   : form -> FApi.backward

(* -------------------------------------------------------------------- *)
val t_hoareF_fun_def   : FApi.backward
val t_choareF_fun_def  : FApi.backward
val t_bdhoareF_fun_def : FApi.backward
val t_equivF_fun_def   : FApi.backward

(* -------------------------------------------------------------------- *)
val t_equivF_abs_upto : form -> form -> form -> FApi.backward

(* -------------------------------------------------------------------- *)
val t_fun : form -> inv_inf option -> FApi.backward
