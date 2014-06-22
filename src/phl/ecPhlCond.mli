(* Copyright (c) - 2012-2014 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-B license *)

(* -------------------------------------------------------------------- *)
open EcCoreGoal.FApi

(* -------------------------------------------------------------------- *)
val t_hoare_cond   : backward
val t_bdhoare_cond : backward
val t_equiv_cond   : bool option -> backward

(* -------------------------------------------------------------------- *)
val process_cond : bool option -> backward
