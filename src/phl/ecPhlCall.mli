(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2015 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-C license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcParsetree
open EcFol
open EcCoreGoal.FApi

(* -------------------------------------------------------------------- *)
val wp2_call :
     EcEnv.env -> form -> form
  -> EcModules.lvalue option * EcPath.xpath * EcTypes.expr list
  -> EcPV.PV.t
  -> EcModules.lvalue option * EcPath.xpath * EcTypes.expr list
  -> EcPV.PV.t
  -> EcMemory.memory -> EcMemory.memory -> form
  -> EcEnv.LDecl.hyps -> form

val t_hoare_call   : form -> form -> backward
val t_bdhoare_call : form -> form -> form option -> backward
val t_equiv_call   : form -> form -> backward
val t_equiv_call1  : side -> form -> form -> backward

(* -------------------------------------------------------------------- *)
val process_call : oside -> call_info fpattern -> backward
