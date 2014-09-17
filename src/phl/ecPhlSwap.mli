(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2014 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-C license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcLocation
open EcParsetree
open EcCoreGoal.FApi

(* -------------------------------------------------------------------- *)
val t_hoare_swap   : int -> int -> int -> backward
val t_bdhoare_swap : int -> int -> int -> backward
val t_equiv_swap   : bool -> int -> int -> int -> backward

(* -------------------------------------------------------------------- *)
val process_swap : (bool option * swap_kind) located list -> backward
