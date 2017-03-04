(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2017 - Inria
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcSymbols
open EcCoreGoal

(* -------------------------------------------------------------------- *)
val t_pr_rewrite_i : symbol *  EcFol.form option -> FApi.backward
val t_pr_rewrite : symbol * EcParsetree.pformula option -> FApi.backward

