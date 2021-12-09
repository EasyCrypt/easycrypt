(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2021 - Inria
 * Copyright (c) - 2012--2021 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcFol
open EcCoreGoal.FApi

(* -------------------------------------------------------------------- *)
val t_hoare_app   : codepos1 -> form -> backward
val t_bdhoare_app : codepos1 -> form tuple6 -> backward
val t_equiv_app   : codepos1 pair -> form -> backward
val t_equiv_app_onesided : side -> codepos1 -> form -> form -> backward

(* -------------------------------------------------------------------- *)
val process_app : app_info -> backward
