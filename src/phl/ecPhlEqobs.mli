(* Copyright (c) - 2012-2014 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-B license *)

(* -------------------------------------------------------------------- *)
open EcUtils
open EcPath
open EcFol
open EcParsetree
open EcCoreGoal
open EcCoreGoal.FApi

(* -------------------------------------------------------------------- *)
val mk_inv_spec : proofenv -> EcEnv.env -> form -> xpath -> xpath -> form
val process_eqobs_in : pformula option tuple3 -> backward
