(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2014 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-C license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcSymbols
open EcParsetree
open EcInductive
open EcEnv

(* -------------------------------------------------------------------- *)
type rcerror =
| RCE_TypeError        of EcTyping.tyerror
| RCE_DuplicatedField  of symbol
| RCE_InvalidFieldType of symbol * EcTyping.tyerror

exception RcError of EcLocation.t * EcEnv.env * rcerror

(* -------------------------------------------------------------------- *)
val rcerror : EcLocation.t -> EcEnv.env -> rcerror -> 'a
val pp_rcerror : EcEnv.env -> Format.formatter -> rcerror -> unit

(* -------------------------------------------------------------------- *)
val trans_record : env -> ptydname -> precord -> record
