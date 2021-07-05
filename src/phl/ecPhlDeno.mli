(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcParsetree
open EcFol
open EcCoreGoal.FApi

(* -------------------------------------------------------------------- *)
val t_phoare_deno : form -> form -> backward
val t_equiv_deno  : form -> form -> backward

(* -------------------------------------------------------------------- *)
type denoff = deno_ppterm * bool * pformula option

val process_deno : [`PHoare | `Equiv] -> denoff -> backward
