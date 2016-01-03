(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2016 - Inria
 * 
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcLocation
open EcSymbols
open EcParsetree

(* -------------------------------------------------------------------- *)
type tperror =
| TPE_Typing of EcTyping.tyerror
| TPE_TyNotClosed
| TPE_DuplicatedConstr of symbol

exception TransPredError of EcLocation.t * EcEnv.env * tperror

val tperror : EcLocation.t -> EcEnv.env -> tperror -> 'a

(* -------------------------------------------------------------------- *)
val trans_preddecl : EcEnv.env -> ppredicate located -> EcDecl.operator
