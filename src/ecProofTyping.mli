(* -------------------------------------------------------------------- *)
open EcParsetree
open EcIdent
open EcDecl
open EcEnv
open EcCoreGoal
open EcMatching.Position
open EcAst

(* -------------------------------------------------------------------- *)
type ptnenv = ty Mid.t * EcUnify.unienv
type metavs = EcFol.form EcSymbols.Msym.t

(* Top-level typing functions, but applied in the context of a
 * proof-environment. See the [Exn] module for more information. *)

val unienv_of_hyps : LDecl.hyps -> EcUnify.unienv
val pf_check_tvi   : proofenv -> ty_params -> EcUnify.tvi -> unit

(* Typing in the environment implied by [LDecl.hyps]. *)
val process_form_opt : ?mv:metavs -> LDecl.hyps -> pformula -> ty option -> form
val process_form     : ?mv:metavs -> LDecl.hyps -> pformula -> ty -> form
val process_formula  : ?mv:metavs -> LDecl.hyps -> pformula -> form
val process_exp      : LDecl.hyps -> [`InProc|`InOp] -> ty option -> pexpr -> expr
val process_pattern  : LDecl.hyps -> pformula -> ptnenv * form

(* Typing in the [LDecl.hyps] implied by the proof env.
 * Typing exceptions are recasted in the proof env. context *)
val pf_process_form_opt : proofenv -> ?mv:metavs -> LDecl.hyps -> ty option -> pformula -> form
val pf_process_form     : proofenv -> ?mv:metavs -> LDecl.hyps -> ty -> pformula -> form
val pf_process_formula  : proofenv -> ?mv:metavs -> LDecl.hyps -> pformula -> form
val pf_process_xreal    : proofenv -> ?mv:metavs -> LDecl.hyps -> pformula -> form

val pf_process_exp      : proofenv -> LDecl.hyps -> [`InProc|`InOp] -> ty option -> pexpr -> expr
val pf_process_pattern  : proofenv -> LDecl.hyps -> pformula -> ptnenv * form

(* Typing in the [proofenv] implies for the [tcenv].
 * Typing exceptions are recasted in the proof env. context *)
val tc1_process_form_opt : ?mv:metavs -> tcenv1 -> ty option -> pformula -> form
val tc1_process_form     : ?mv:metavs -> tcenv1 -> ty -> pformula -> form
val tc1_process_formula  : ?mv:metavs -> tcenv1 -> pformula -> form
val tc1_process_exp      : tcenv1 -> [`InProc|`InOp] -> ty option -> pexpr -> expr
val tc1_process_pattern  : tcenv1 -> pformula -> ptnenv * form

(* Same as previous functions, but for *HL contexts *)
val tc1_process_Xhl_form     : ?side:side -> tcenv1 -> ty -> pformula -> memtype * ss_inv
val tc1_process_Xhl_formula  : ?side:side -> tcenv1 -> pformula -> memtype * ss_inv
val tc1_process_Xhl_formula_xreal : tcenv1 -> pformula -> memtype * ss_inv

val tc1_process_Xhl_exp      : tcenv1 -> oside -> ty option -> pexpr -> expr

val tc1_process_prhl_form_opt: tcenv1 -> ty option -> pformula -> ts_inv
val tc1_process_prhl_form    : tcenv1 -> ty -> pformula -> ts_inv
val tc1_process_prhl_formula : tcenv1 -> pformula -> ts_inv

val tc1_process_prhl_stmt :
     ?map:EcTyping.ismap -> tcenv1 -> side -> pstmt -> stmt

val tc1_process_Xhl_stmt :
     ?map:EcTyping.ismap -> tcenv1 -> pstmt -> stmt

val tc1_process_codepos_range : tcenv1 -> oside * pcodepos_range -> codepos_range
val tc1_process_codepos : tcenv1 -> oside * pcodepos -> codepos
val tc1_process_codepos1 : tcenv1 -> oside * pcodepos1 -> codepos1

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
