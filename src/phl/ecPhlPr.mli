(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2016 - Inria
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcTypes
open EcFol
open EcCoreGoal.FApi

(* -------------------------------------------------------------------- *)
val t_hoare_ppr   : backward
val t_bdhoare_ppr : backward
val t_equiv_ppr   : ty -> form -> form -> backward

(* -------------------------------------------------------------------- *)
val t_prbounded : bool -> backward
val t_prfalse   : backward

(* -------------------------------------------------------------------- *)
val process_ppr : (pformula tuple2) option -> backward
