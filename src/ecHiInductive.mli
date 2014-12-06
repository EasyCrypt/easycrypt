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

type dterror =
| DTE_TypeError       of EcTyping.tyerror
| DTE_DuplicatedCtor  of symbol
| DTE_InvalidCTorType of symbol * EcTyping.tyerror
| DTE_NonPositive
| DTE_Empty

(* -------------------------------------------------------------------- *)
exception RcError of EcLocation.t * EcEnv.env * rcerror
exception DtError of EcLocation.t * EcEnv.env * dterror

(* -------------------------------------------------------------------- *)
val rcerror : EcLocation.t -> EcEnv.env -> rcerror -> 'a
val dterror : EcLocation.t -> EcEnv.env -> dterror -> 'a

(* -------------------------------------------------------------------- *)
val pp_rcerror : EcEnv.env -> Format.formatter -> rcerror -> unit
val pp_dterror : EcEnv.env -> Format.formatter -> dterror -> unit

(* -------------------------------------------------------------------- *)
val trans_record : env -> ptydname -> precord -> record

(* -------------------------------------------------------------------- *)
val trans_datatype : env -> ptydname -> pdatatype -> datatype
