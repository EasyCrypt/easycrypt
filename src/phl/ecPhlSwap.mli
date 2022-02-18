(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2021 - Inria
 * Copyright (c) - 2012--2021 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcLocation
open EcParsetree
open EcCoreGoal.FApi

(* -------------------------------------------------------------------- *)
val t_hoare_swap   : int -> int -> int -> backward
val t_choare_swap  : int -> int -> int -> backward
val t_bdhoare_swap : int -> int -> int -> backward
val t_equiv_swap   : side -> int -> int -> int -> backward

(* -------------------------------------------------------------------- *)
val process_swap : (oside * swap_kind) located list -> backward

(* -------------------------------------------------------------------- *)
val process_interleave : interleave_info located -> backward
