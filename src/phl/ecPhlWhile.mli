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
val t_hoare_while      : form -> backward
val t_choare_while     : form -> form -> form -> cost -> backward
val t_bdhoare_while    : form -> form -> backward
val t_equiv_while_disj : side -> form -> form -> backward
val t_equiv_while      : form -> backward

(* -------------------------------------------------------------------- *)
val process_while : oside -> while_info -> backward
val process_async_while : async_while_info -> backward
