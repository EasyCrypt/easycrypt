(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2015 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-C license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcPath
open EcParsetree
open EcFol
open EcCoreGoal.FApi

(* -------------------------------------------------------------------- *)
val t_failure_event :
     int
  -> form -> form -> form -> form
  -> (xpath * form) list
  -> form
  -> backward

(* -------------------------------------------------------------------- *)
val process_fel : int -> fel_info -> backward
