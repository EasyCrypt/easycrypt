(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2014 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-C license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcParsetree
open EcCoreGoal
open EcHiGoal

(* -------------------------------------------------------------------- *)
val process1 : ttenv -> ptactic -> FApi.backward
val process  : ttenv -> ptactic list -> proof -> proof
