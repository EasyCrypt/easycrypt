(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2021 - Inria
 * Copyright (c) - 2012--2021 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcParsetree
open EcCoreGoal
open EcHiGoal

(* -------------------------------------------------------------------- *)
val process1 : ttenv -> ptactic -> FApi.backward
val process  : ttenv -> ptactic list -> proof -> (handle * handle list) * proof
