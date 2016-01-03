(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2016 - Inria
 * 
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcSymbols
open EcParsetree
open EcLocation
open EcDecl
open EcEnv

(* -------------------------------------------------------------------- *)
type nterror =
| NTE_Typing        of EcTyping.tyerror
| NTE_TyNotClosed
| NTE_DupIdent
| NTE_UnknownBinder of symbol
| NTE_AbbrevIsVar

exception NotationError of EcLocation.t * EcEnv.env * nterror

val nterror : EcLocation.t -> env -> nterror -> 'a

(* -------------------------------------------------------------------- *)
val trans_notation : env -> pnotation located -> unit
val trans_abbrev : env -> pabbrev located -> symbol * operator
