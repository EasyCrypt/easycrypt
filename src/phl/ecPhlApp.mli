(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2016 - Inria
 * 
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcFol
open EcCoreGoal.FApi

(* -------------------------------------------------------------------- *)
val t_hoare_app   : int -> form -> backward
val t_bdhoare_app : int -> form tuple6 -> backward
val t_equiv_app   : int * int -> form -> backward
val t_equiv_app_onesided : side -> int -> form -> form -> backward

(* -------------------------------------------------------------------- *)
val process_app : app_info -> backward
