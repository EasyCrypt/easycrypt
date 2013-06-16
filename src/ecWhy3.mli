(* -------------------------------------------------------------------- *)
open EcSymbols

type env

val empty : env

type rebinding_item
type rebinding = rebinding_item list

val rebind : env -> rebinding -> env

(* importing why3 theory *)

type renaming_kind =
  | RDts
  | RDls
  | RDpr

type renaming_decl = (string list * renaming_kind * symbol) list

val import_w3 :
    env -> EcPath.path ->
      Why3.Theory.theory ->
        renaming_decl -> EcTheory.theory * rebinding_item

val distr_theory : Why3.Theory.theory

val add_ty : env -> EcPath.path -> EcDecl.tydecl -> env * rebinding

val add_op :
    env -> EcPath.path -> EcDecl.operator -> env * rebinding

val add_ax : env -> EcPath.path -> EcDecl.axiom -> env * rebinding

val add_mod_exp :
    env -> EcPath.path -> EcModules.module_expr -> env * rebinding

(*****************************************************************************)
exception CanNotTranslate of string

val check_goal : 
  (EcIdent.t -> EcModules.module_type -> EcPath.Sm.t -> EcModules.module_expr) ->
  env -> EcProvers.prover_infos -> EcBaseLogic.l_decl -> bool
