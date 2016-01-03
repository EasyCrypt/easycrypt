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
val t_phoare_deno : form -> form -> backward
val t_equiv_deno  : form -> form -> backward

(* -------------------------------------------------------------------- *)
type denoff = ((pformula option) tuple2) gppterm * bool * pformula option

val process_deno : [`PHoare | `Equiv] -> denoff -> backward
