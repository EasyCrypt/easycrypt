(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2015 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-C license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcSymbols
open EcIdent
open EcParsetree
open EcInductive
open EcEnv

(* -------------------------------------------------------------------- *)
type rcerror =
| RCE_TypeError        of EcTyping.tyerror
| RCE_DuplicatedField  of symbol
| RCE_InvalidFieldType of symbol * EcTyping.tyerror
| RCE_Empty

type dterror =
| DTE_TypeError       of EcTyping.tyerror
| DTE_DuplicatedCtor  of symbol
| DTE_InvalidCTorType of symbol * EcTyping.tyerror
| DTE_NonPositive
| DTE_Empty

type fxerror =
| FXE_TypeError of EcTyping.tyerror
| FXE_EmptyMatch
| FXE_MatchParamsMixed
| FXE_MatchParamsDup
| FXE_MatchParamsUnk
| FXE_MatchNonLinear
| FXE_MatchDupBranches
| FXE_MatchPartial
| FXE_CtorUnk
| FXE_CtorAmbiguous
| FXE_CtorInvalidArity of (int * int)

(* -------------------------------------------------------------------- *)
exception RcError of EcLocation.t * EcEnv.env * rcerror
exception DtError of EcLocation.t * EcEnv.env * dterror
exception FxError of EcLocation.t * EcEnv.env * fxerror

(* -------------------------------------------------------------------- *)
val rcerror : EcLocation.t -> EcEnv.env -> rcerror -> 'a
val dterror : EcLocation.t -> EcEnv.env -> dterror -> 'a
val fxerror : EcLocation.t -> EcEnv.env -> fxerror -> 'a

(* -------------------------------------------------------------------- *)
val pp_rcerror : EcEnv.env -> Format.formatter -> rcerror -> unit
val pp_dterror : EcEnv.env -> Format.formatter -> dterror -> unit

(* -------------------------------------------------------------------- *)
val trans_record : env -> ptydname -> precord -> record

(* -------------------------------------------------------------------- *)
val trans_datatype : env -> ptydname -> pdatatype -> datatype

(* -------------------------------------------------------------------- *)
type matchfix_t =  {
  mf_name     : ident;
  mf_codom    : EcTypes.ty;
  mf_args     : (ident * EcTypes.ty) list;
  mf_recs     : int list;
  mf_branches : EcDecl.opbranches;
}

val trans_matchfix :
     ?close:bool
  -> EcEnv.env
  -> EcUnify.unienv
  -> psymbol
  -> ptybindings * pty * pop_branch list
  -> EcTypes.ty * matchfix_t
