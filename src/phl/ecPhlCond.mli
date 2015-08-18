(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2015 - IMDEA Software Institute
 * Copyright (c) - 2012--2015 - Inria
 * 
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcParsetree
open EcCoreGoal.FApi

(* -------------------------------------------------------------------- *)
val t_hoare_cond   : backward
val t_bdhoare_cond : backward
val t_equiv_cond   : oside -> backward

(* -------------------------------------------------------------------- *)
val process_cond : pcond_info -> backward
