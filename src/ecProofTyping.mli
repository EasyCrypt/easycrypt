(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2016 - Inria
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcParsetree
open EcIdent
open EcTypes
open EcFol
open EcDecl
open EcModules
open EcEnv
open EcCoreGoal

(* -------------------------------------------------------------------- *)
type ptnenv = ty Mid.t * EcUnify.unienv

(* Top-level typing functions, but applied in the context of a
 * proof-environment. See the [Exn] module for more information. *)

val unienv_of_hyps : LDecl.hyps -> EcUnify.unienv
val pf_check_tvi   : proofenv -> ty_params -> EcUnify.tvi -> unit

(* Typing in the environment implied by [LDecl.hyps]. *)
val process_form_opt : LDecl.hyps -> pformula -> ty option -> form
val process_form     : LDecl.hyps -> pformula -> ty -> form
val process_formula  : LDecl.hyps -> pformula -> form
val process_exp      : LDecl.hyps -> [`InProc|`InOp] -> ty option -> pexpr -> expr
val process_pattern  : LDecl.hyps -> pformula -> ptnenv * form

(* Typing in the [LDecl.hyps] implied by the proof env.
 * Typing exceptions are recasted in the proof env. context *)
val pf_process_form_opt : proofenv -> LDecl.hyps -> ty option -> pformula -> form
val pf_process_form     : proofenv -> LDecl.hyps -> ty -> pformula -> form
val pf_process_formula  : proofenv -> LDecl.hyps -> pformula -> form
val pf_process_exp      : proofenv -> LDecl.hyps -> [`InProc|`InOp] -> ty option -> pexpr -> expr
val pf_process_pattern  : proofenv -> LDecl.hyps -> pformula -> ptnenv * form

(* Typing in the [proofenv] implies for the [tcenv].
 * Typing exceptions are recasted in the proof env. context *)
val tc1_process_form_opt : tcenv1 -> ty option -> pformula -> form
val tc1_process_form     : tcenv1 -> ty -> pformula -> form
val tc1_process_formula  : tcenv1 -> pformula -> form
val tc1_process_exp      : tcenv1 -> [`InProc|`InOp] -> ty option -> pexpr -> expr
val tc1_process_pattern  : tcenv1 -> pformula -> ptnenv * form

(* Same as previous functions, but for PHL contexts *)
val tc1_process_phl_form     : ?side:side -> tcenv1 -> ty -> pformula -> form
val tc1_process_phl_formula  : ?side:side -> tcenv1 -> pformula -> form
val tc1_process_phl_exp      : tcenv1 -> oside -> ty option -> pexpr -> expr

val tc1_process_prhl_form    : tcenv1 -> ty -> pformula -> form
val tc1_process_prhl_formula : tcenv1 -> pformula -> form

val tc1_process_aprhl_form    : tcenv1 -> ty -> pformula -> form
val tc1_process_aprhl_formula : tcenv1 -> pformula -> form

val tc1_process_stmt : tcenv1 -> EcMemory.memtype -> pstmt -> stmt
val tc1_process_prhl_stmt : tcenv1 -> side -> pstmt -> stmt

(* -------------------------------------------------------------------- *)
exception NoMatch

val lazy_destruct :
     ?reduce:bool
  -> EcEnv.LDecl.hyps
  -> (form -> 'a)
  -> (form -> 'a option)

(* -------------------------------------------------------------------- *)
type dproduct = [
  | `Imp    of form * form
  | `Forall of EcIdent.t * gty * form
]

type dexists = [
  | `Exists of EcIdent.t * gty * form
]

val destruct_product: ?reduce:bool -> EcEnv.LDecl.hyps -> form -> dproduct option
val destruct_exists : ?reduce:bool -> EcEnv.LDecl.hyps -> form -> dexists  option

(* -------------------------------------------------------------------- *)
exception NoMatch

type lazyred = [`Full | `NoDelta | `None]

val t_lazy_match:
  ?reduce:lazyred -> (form -> FApi.backward)-> FApi.backward
