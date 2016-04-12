(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2016 - Inria
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcCoreGoal

val t_tohoare : FApi.backward
val t_ofhoare : FApi.backward

val t_toequiv : FApi.backward
val t_ofequiv : FApi.backward

val t_lap : lap_mode -> FApi.backward

val t_while : (pexpr * pexpr) * (pformula pair) * pexpr -> FApi.backward

val t_pweq : pformula -> FApi.backward
