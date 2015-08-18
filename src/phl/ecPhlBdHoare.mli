(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2015 - IMDEA Software Institute
 * Copyright (c) - 2012--2015 - Inria
 * 
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcCoreGoal.FApi

(* -------------------------------------------------------------------- *)
val t_hoare_bd_hoare : backward
val process_bdhoare_split : EcParsetree.bdh_split -> backward
