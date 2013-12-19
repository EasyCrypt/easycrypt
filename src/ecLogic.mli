(* -------------------------------------------------------------------- *)
open EcMaps
open EcSymbols
open EcParsetree
open EcModules
open EcLocation
open EcReduction
open EcBaseLogic
open EcEnv
open EcFol
open EcProvers

(* -------------------------------------------------------------------- *)
type pre_judgment = {
  pj_decl : LDecl.hyps * form;
  pj_rule : (bool * int rnode) option;
}

type judgment_uc = {
  juc_count : int;
  juc_map   : pre_judgment Mint.t;
}

type goals  = judgment_uc * int list
type goal   = judgment_uc * int 
type tactic = goal -> goals 

(* -------------------------------------------------------------------- *)
val cannot_apply : string -> string -> 'a
val tacerror     : ?catchable:bool -> EcBaseLogic.tac_error -> 'a
val tacuerror    : ?catchable:bool -> ('a, Format.formatter, unit, 'b) format4 -> 'a

val set_loc : EcLocation.t -> ('a -> 'b) -> 'a -> 'b

(* -------------------------------------------------------------------- *)
val destruct_product : EcEnv.LDecl.hyps -> EcFol.form ->
  [ `Forall of EcIdent.t * EcFol.gty * EcFol.form
  | `Imp of EcFol.form * EcFol.form
  ]  option

(* -------------------------------------------------------------------- *)
val get_pj     : goal -> pre_judgment
val get_goal   : goal -> LDecl.hyps * form
val get_goal_e : goal -> env * LDecl.hyps * form
val get_concl  : goal -> form
val get_hyps   : goal -> LDecl.hyps
val get_node   : goal -> LDecl.hyps * form
val new_goal   : judgment_uc -> LDecl.hyps * form -> goal

val upd_rule : int rnode -> goal -> goals
val upd_rule_done : int rnode -> goal -> goals

val upd_done : judgment_uc -> judgment_uc

val open_juc  : LDecl.hyps * form -> judgment_uc
val close_juc : judgment_uc -> judgment

val find_all_goals : judgment_uc -> goals

val find_in_hyps : form -> LDecl.hyps -> EcIdent.t

val prove_goal_by : form list -> rule -> tactic

(* -------------------------------------------------------------------- *)
val t_id : string option -> tactic
val t_fail : tactic

val t_reflex : ?reduce:bool -> tactic

val t_focus : tfocus -> tactic -> goals -> goals

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
val t_do     : [`All | `Maybe] -> int option -> tactic -> tactic
val t_try    : tactic -> tactic
val t_or     : tactic -> tactic -> tactic
val t_lor    : tactic list -> tactic

val t_close : tactic -> tactic

val t_rotate : [`Left | `Right] -> int -> goals -> goals

(* -------------------------------------------------------------------- *)
(* TODO : move this in ecEnv.Mod *)
val gen_check_restr : 
  env -> 
  (EcPrinting.PPEnv.t -> 'a EcPrinting.pp) -> 'a ->
  use -> mod_restr -> unit

val check_restr :  EcEnv.env -> EcPath.mpath -> mod_restr -> unit

val check_modtype_restr :
  EcEnv.env -> EcPath.mpath -> module_sig -> module_type -> mod_restr -> unit

(* -------------------------------------------------------------------- *)
type app_arg =
  | AAform of form
  | AAmem  of EcIdent.t
  | AAmp   of EcPath.mpath * EcModules.module_sig 
  | AAnode

type 'a app_arg_cb = LDecl.hyps -> gty option -> 'a -> app_arg

type dofpattern = LDecl.hyps -> form -> form -> (EcIdent.t * form)

val t_hyp : EcIdent.t -> tactic

val t_generalize_hyp  : EcIdent.t -> tactic
val t_generalize_form : ?fpat:dofpattern -> symbol option -> form -> tactic

val t_intros_i : EcIdent.t list -> tactic
val t_intros_1 : EcIdent.t list -> goal -> goal
val t_intros   : EcIdent.t located list -> tactic

val t_elim_hyp : EcIdent.t -> tactic
val t_elim     : tactic

val t_elimT_form : EcTypes.ty list -> EcPath.path -> form -> int -> tactic

val t_case : form -> tactic

val t_rewrite_hyp  : ?fpat:dofpattern -> rwside -> EcIdent.t -> app_arg list -> tactic
val t_rewrite_glob : ?fpat:dofpattern -> rwside -> EcPath.path -> EcTypes.ty list -> app_arg list -> tactic
val t_rewrite_form : ?fpat:dofpattern -> rwside -> form -> app_arg list -> tactic
val t_rewrite_node : ?fpat:dofpattern -> goal * int list -> rwside -> int -> goals

val t_simplify : reduction_info -> tactic
val t_simplify_nodelta : tactic

val t_true  : tactic
val t_split : tactic

val t_left  : tactic
val t_right : tactic

val t_congr : form -> (form * form) list * EcTypes.ty -> tactic

val t_smt : strict:bool -> bool * hints -> EcProvers.prover_infos -> tactic

val t_cut : form -> tactic

val t_clear : EcIdent.Sid.t -> tactic

val t_glob : EcPath.path -> EcTypes.ty list -> tactic

val t_use : int -> 'a -> goal -> judgment_uc * 'a

val t_change : form -> tactic

val t_subst_all : tactic
val t_subst1    : form option -> tactic

val t_assumption : tactic

val t_progress : tactic -> tactic

val t_build : goal -> (EcIdent.t * form) * tactic

val t_intros_elim : int -> tactic
val t_progress_one : tactic

val t_logic_trivial : tactic

val t_admit : tactic

(* -------------------------------------------------------------------- *)
val gen_t_apply_hyp : 
     'a app_arg_cb -> EcIdent.t -> 'a list -> tactic

val gen_t_apply_glob :
     'a app_arg_cb -> EcPath.path -> EcTypes.ty list
  -> 'a list -> tactic

val t_apply_glob : EcPath.path -> EcTypes.ty list -> app_arg list -> tactic

val gen_t_apply_form :
     'a app_arg_cb -> form -> 'a list -> tactic

val gen_t_exists : 'a app_arg_cb -> 'a list -> tactic

(* -------------------------------------------------------------------- *)
val mkn_hyp  : judgment_uc -> LDecl.hyps -> EcIdent.t -> goal
val mkn_glob : judgment_uc -> LDecl.hyps -> EcPath.path -> EcTypes.ty list -> goal

val mkn_apply : 'a app_arg_cb -> goal -> 'a list -> goal * int list
