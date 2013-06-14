(* -------------------------------------------------------------------- *)
open EcMaps
open EcUtils
open EcSymbols
open EcModules
open EcLocation
open EcReduction
open EcBaseLogic
open EcEnv
open EcFol

(* -------------------------------------------------------------------- *)
type pre_judgment = {
  pj_decl : LDecl.hyps * form;
  pj_rule : (bool * int rule) option;
}

type judgment_uc = {
  juc_count : int;
  juc_map   : pre_judgment Mint.t;
}

type goals  = judgment_uc * int list
type goal   = judgment_uc * int 
type tactic = goal -> goals 

(* -------------------------------------------------------------------- *)
type tac_error =
  | UnknownAx             of EcPath.path
  | NotAHypothesis        of EcIdent.t
  | UnknownElims          of form
  | UnknownIntros         of form
  | UnknownSplit          of form
  | UnknownRewrite        of form
  | CannotClearConcl      of EcIdent.t * form
  | CannotReconizeElimT
  | TooManyArgument
  | NoHypToSubst          of EcIdent.t option
  | CannotProve           of (LDecl.hyps * form)
  | InvalNumOfTactic      of int * int
  | NotPhl                of bool option
  | NoSkipStmt
  | InvalidCodePosition   of string * int * int * int
  | CanNotApply           of string * string
  | InvalidName           of string
  | User                  of string

exception TacError of tac_error

val cannot_apply : string -> string -> 'a
val tacerror     : tac_error -> 'a
val tacuerror    : ('a, Format.formatter, unit, 'b) format4 -> 'a

val set_loc : EcLocation.t -> ('a -> 'b) -> 'a -> 'b

(* -------------------------------------------------------------------- *)
val get_goal  : goal -> LDecl.hyps * form
val get_concl : goal -> form
val get_hyps  : goal -> LDecl.hyps
val get_node  : goal -> LDecl.hyps * form
val get_pj    : goal -> pre_judgment

val new_goal : judgment_uc -> LDecl.hyps * form -> goal

val upd_rule : int rule -> goal -> goals
val upd_rule_done : int rule -> goal -> goals

val upd_done : judgment_uc -> judgment_uc

val open_juc  : LDecl.hyps * form -> judgment_uc
val close_juc : judgment_uc -> judgment

val find_all_goals : judgment_uc -> goals

val tyenv_of_hyps :  EcEnv.env -> LDecl.hyps -> EcEnv.env

val find_in_hyps : EcEnv.env -> form -> LDecl.hyps -> EcIdent.t

(* -------------------------------------------------------------------- *)
val t_id : string option -> tactic

val t_on_first : tactic -> goals -> goals
val t_on_last  : tactic -> goals -> goals

val t_on_firsts : tactic -> int -> goals -> goals
val t_on_lasts  : tactic -> int -> goals -> goals

val t_subgoal  : tactic list -> goals -> goals
val t_on_goals : tactic -> goals -> goals

val t_seq_subgoal : tactic -> tactic list -> tactic

val t_seq  : tactic -> tactic -> tactic
val t_lseq : tactic list -> tactic

val t_repeat : tactic -> tactic
val t_do     : bool -> int option -> tactic -> tactic
val t_try    : tactic -> tactic
val t_or     : tactic -> tactic -> tactic

val t_close : tactic -> tactic

val t_rotate : [`Left | `Right] -> int -> goals -> goals

(* -------------------------------------------------------------------- *)
val check_modtype_restr :
  EcEnv.env -> EcPath.mpath -> module_sig -> module_type -> EcPath.Sm.t -> unit

(* -------------------------------------------------------------------- *)
type app_arg =
  | AAform of form
  | AAmem  of EcIdent.t
  | AAmp   of EcPath.mpath * EcModules.module_sig 
  | AAnode

type 'a app_arg_cb = EcEnv.env -> LDecl.hyps -> gty option -> 'a -> app_arg

val t_hyp : EcEnv.env -> EcIdent.t -> tactic

val t_generalize_hyp  : EcEnv.env -> EcIdent.t -> tactic
val t_generalize_form : symbol option -> EcEnv.env -> form -> tactic

val t_intros_i : EcEnv.env -> EcIdent.t list -> tactic
val t_intros   : EcEnv.env -> EcIdent.t located list -> tactic

val t_elim_hyp : EcEnv.env -> EcIdent.t -> tactic
val t_elim     : EcEnv.env -> form -> tactic

val t_elimT : EcEnv.env -> form -> EcPath.path -> tactic

val t_case : EcEnv.env -> form -> tactic

val t_rewrite_hyp  : EcEnv.env -> bool -> EcIdent.t -> app_arg list -> tactic
val t_rewrite_node : EcEnv.env -> goal * int list -> bool -> int -> goals

val t_simplify : EcEnv.env -> reduction_info -> tactic
val t_simplify_nodelta : EcEnv.env -> tactic

val t_split : EcEnv.env -> tactic

val t_left  : EcEnv.env -> tactic
val t_right : EcEnv.env -> tactic

val t_trivial : EcProvers.prover_infos -> EcEnv.env -> tactic

val t_cut : EcEnv.env -> form -> tactic

val t_clear : EcIdent.Sid.t -> tactic

val t_glob : EcEnv.env -> EcPath.path -> EcTypes.ty list -> tactic

val t_use : EcEnv.env -> int -> 'a -> goal -> judgment_uc * 'a

val t_change : EcEnv.env -> form -> tactic

val t_subst_all : EcEnv.env -> tactic
val t_subst1    : EcEnv.env -> form option -> tactic

val t_progress : EcEnv.env -> tactic -> tactic

val t_field      : form tuple7 -> form * form -> tactic
val t_field_simp : form tuple7 -> form -> tactic

val t_admit : tactic

(* -------------------------------------------------------------------- *)
val gen_t_apply_hyp : 
     'a app_arg_cb -> EcEnv.env -> EcIdent.t -> 'a list -> tactic

val gen_t_apply_glob :
     'a app_arg_cb -> EcEnv.env -> EcPath.path -> EcTypes.ty list
  -> 'a list -> tactic

val gen_t_apply_form :
     'a app_arg_cb -> EcEnv.env -> form -> 'a list -> tactic

val gen_t_exists : 'a app_arg_cb -> EcEnv.env -> 'a list -> tactic

(* -------------------------------------------------------------------- *)
val mkn_hyp  : judgment_uc -> LDecl.hyps -> EcIdent.t -> goal
val mkn_glob : EcEnv.env -> judgment_uc -> LDecl.hyps -> EcPath.path -> EcTypes.ty list -> goal

val mkn_apply : 'a app_arg_cb -> EcEnv.env -> goal -> 'a list -> goal * int list
