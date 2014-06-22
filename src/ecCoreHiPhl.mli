(* Copyright (c) - 2012-2014 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-B license *)

(* -------------------------------------------------------------------- *)
open EcParsetree
open EcTypes
open EcModules
open EcFol
open EcLogic

(* -------------------------------------------------------------------- *)
val process_phl_form     : ty -> goal -> pformula -> form
val process_phl_formula  : goal -> pformula -> form
val process_phl_exp      : bool option -> pexpr -> ty option -> goal -> expr

val process_prhl_form    : ty -> goal -> pformula -> form
val process_prhl_formula : goal -> pformula -> form
val process_prhl_post    : goal -> pformula -> form

val process_prhl_stmt    : bool -> goal -> pstmt -> stmt

