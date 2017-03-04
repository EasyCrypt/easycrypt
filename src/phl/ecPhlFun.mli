(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2017 - Inria
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

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
     EcEnv.env -> xpath -> funsig -> memory
  -> EcPV.PVM.subst
  -> EcPV.PVM.subst

(* -------------------------------------------------------------------- *)
type p_upto_info = pformula * pformula * (pformula option)

val process_fun_def       : FApi.backward
val process_fun_abs       : pformula -> FApi.backward
val process_fun_upto_info : p_upto_info -> tcenv1 -> form tuple3
val process_fun_upto      : p_upto_info -> FApi.backward
val process_fun_to_code   : FApi.backward

(* -------------------------------------------------------------------- *)
module FunAbsLow : sig
  val hoareF_abs_spec :
       proofenv -> EcEnv.env -> xpath -> form
    -> form * form * form list

  val bdhoareF_abs_spec :
       proofenv -> EcEnv.env -> xpath -> form
    -> form * form * form list

  val equivF_abs_spec :
       proofenv -> EcEnv.env -> xpath -> xpath -> form
    -> form * form * form list
end

(* -------------------------------------------------------------------- *)
val t_hoareF_abs   : form -> FApi.backward
val t_bdhoareF_abs : form -> FApi.backward
val t_equivF_abs   : form -> FApi.backward

(* -------------------------------------------------------------------- *)
val t_hoareF_fun_def   : FApi.backward
val t_bdhoareF_fun_def : FApi.backward
val t_equivF_fun_def   : FApi.backward

(* -------------------------------------------------------------------- *)
val t_equivF_abs_upto : form -> form -> form -> FApi.backward

(* -------------------------------------------------------------------- *)
val t_fun : form -> FApi.backward
