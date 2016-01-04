(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2016 - Inria
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcLocation
open EcParsetree
open EcCoreGoal.FApi

(* -------------------------------------------------------------------- *)
val t_hoare_swap   : int -> int -> int -> backward
val t_bdhoare_swap : int -> int -> int -> backward
val t_equiv_swap   : side -> int -> int -> int -> backward

(* -------------------------------------------------------------------- *)
val process_swap : (oside * swap_kind) located list -> backward
