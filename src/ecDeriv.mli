
val rhl_cntr : int ref

val forget_all_from : int -> unit
val un_save : int -> unit
val get_proof_depth : unit -> int

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** {2 Properties} *)

(** This is a property like [f1 ~ f2 : pre ==> post] *)
type spec_fct

(* type spec *)

(** get main elements from an [spec_fct] *)
val equiv_of_spec : spec_fct -> AstLogic.equiv

(** While proving an [spec_fct], a prove tree is built: 
* it is composed of elements called [goal]. *)
type goal


(* type appgoal *)

val equiv_of_goal : goal ->
  Fol.pred * Global.venv * Ast.stmt * Global.venv * Ast.stmt * Fol.pred * 
    (Fol.term * Fol.term) option


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** {2 Global state management} *)

(** The global state contains proved specifications and 
    specifications to prove *)

(** add the [spec_fct] if the proved specifications if it is proved *)
val add_spec : spec_fct -> spec_fct
(** add the current specification (to prove) in the proved specifications *)
val save : unit -> unit
val abort : unit -> string

(** Find a property by its name in the global state. *)
val find_named_spec : string -> spec_fct option

(** Find all the specification on [f1~f2] in the global state. *)
val find_all_spec : Ast.fct -> Ast.fct -> spec_fct list

val new_spec_def : ?cur:bool -> string -> AstLogic.equiv -> spec_fct * goal
val new_spec_adv : 
  string -> FunLogic.inv -> Ast.fct -> Ast.fct -> spec_fct list -> spec_fct
val new_spec_sub : 
  (unit -> string) -> spec_fct -> Fol.pred -> Fol.pred -> 
  (Fol.term * Fol.term) option ->
  spec_fct
val spec_id : spec_fct -> int
val spec_name : spec_fct -> string

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** {3 Functions over goals } *)

(** return the current goal *)
val cur_goal : unit -> goal

(** return a fresh unproved goal *)
val init_goal : 
  Fol.pred -> Global.venv -> Ast.stmt -> 
  Global.venv -> Ast.stmt -> Fol.pred 
  -> (Fol.term * Fol.term) option 
  -> goal


(** return a fresh unproved goal identical to [goal] *)
val copy_goal : goal -> goal

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** {2 Tactics} *)

(** {3 Tactic definitions} 
* A tactic is a function that applies a [rule] on a goal,
* and possibly generate subgoals (i.e unproved goal). 
*)


type tactic = goal -> goal list 

(* applies the tactic to the current goal *)
val cur_tac : tactic -> goal list

(* do nothing *)
val id_tac : tactic
(* fail *)
val fail_tac : string -> tactic

(* Warning : remove the proof of the goal *)
val reset_tac : tactic

(** [set_proof gp gu] try to use the proof of gp to prove the gu. *)
val set_proof_tac : goal -> tactic

(** [try_tac t g] try to apply t on g if t fail return g unchanged. *)
val try_tac : tactic -> tactic

(** [or_tac t1 t2 g] try to apply t1 on g if fail apply t2. *)
val or_tac : tactic -> tactic -> tactic

(** [seq_tac t1 t2 g] apply t1 on g and t2 on the generated subgoal. *)
val seq_tac : tactic -> tactic -> tactic

(** [subgoal_tac lt lg] apply lt on lg.
 The two list should have the same length. *)
val subgoal_tac : tactic list -> goal list -> goal list

val on_subgoal_tac : tactic -> goal list -> goal list

val seq_subgoal_tac : tactic -> tactic list -> tactic

(** [repeat_tac t g] apply t on g and recursivelly on the generated
    subgoals until it fail *)
val repeat_tac : tactic -> tactic

val do_tac : int -> tactic -> tactic

(** admit the goal *)
val admit_tac : tactic

(** {3 pRHL rules } *)

(* val sub_tac : Fol.pred -> Fol.pred -> tactic *)

val set_tac : bool -> int -> 
    EcUtil.pos * string -> AstYacc.type_exp -> AstYacc.p_exp ->
    tactic

val case_tac : ApiTypes.side * AstYacc.p_exp -> tactic

val reduce_cond_tac : bool -> int -> bool -> tactic

val cond_tac : ApiTypes.side -> tactic

val eqobs_in : (Ast.fct -> Ast.fct -> EcTerm.Vset2.t * EcTerm.Vset2.t) -> 
  Fol.pred -> Ast.stmt -> Ast.stmt -> EcTerm.Vset2.t -> 
  Ast.stmt * Ast.stmt * EcTerm.Vset2.t

val add_eqs : Ast.exp -> Ast.exp -> EcTerm.Vset2.t -> EcTerm.Vset2.t

val eqobs_in_tac : 
    int list -> (EcTerm.Vset2.t * Fol.pred) -> tactic

val while_tac : ApiTypes.side * AstYacc.p_fol *
           (AstYacc.p_exp * AstYacc.p_exp) option -> tactic
val whilerev_tac : ApiTypes.side * AstYacc.p_fol *
           (AstYacc.p_exp * AstYacc.p_exp) option-> tactic

val whileapp_tac : AstYacc.p_exp * AstYacc.p_exp * AstYacc.p_exp * AstYacc.p_exp
  * AstYacc.p_exp * AstYacc.p_fol -> tactic

val whileappgen_tac : (EcUtil.pos * string) * AstYacc.p_exp * AstYacc.p_exp * 
  AstYacc.p_exp * int * int * AstYacc.p_exp * AstYacc.p_exp * AstYacc.p_fol 
  -> tactic

val popspec_tac : ApiTypes.side * (EcUtil.pos * string) * AstYacc.p_exp list -> tactic

val prhl_tac :  tactic
val aprhl_tac : tactic



val unroll_tac : bool -> int -> tactic



val splitwhile_tac : bool -> int -> AstYacc.p_exp -> tactic

val app_tac : int * int -> Fol.pred -> 
  (AstYacc.p_exp * AstYacc.p_exp * AstYacc.p_exp * AstYacc.p_exp) option
  -> tactic

val wp_asgn_tac : tactic

val wp_simpl_tac : ?pos:(int*int) option -> tactic

val sp_simpl_tac : ?pos:(int*int) option -> tactic

val wp_call_tac : int -> tactic

val wp_rnd_tac : (string option * AstYacc.p_exp) AstLogic.rnd_info -> tactic

val sp_rnd_tac : (string option * AstYacc.p_exp) AstLogic.rnd_info -> tactic

val wp_rnd_disj_tac : ApiTypes.side -> tactic

val pre_false_tac : tactic

val post_true_tac : tactic

val not_modify_tac : bool -> Fol.pred -> tactic 

val simplify_tac : bool -> tactic


val unfold_tac : string list -> tactic

(** {3 program transformations} *)

val inline_tac : bool -> EcInline.cond -> tactic  

val ifsync_tac : int -> int -> tactic

val ifneg_tac : bool -> int -> tactic

val swap_tac : ApiTypes.side * AstLogic.swap_kind -> tactic

val derandomize_tac : bool -> tactic


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** {2 Printing} *)

val pp_goal :  Format.formatter -> goal -> unit
val pp_cur_goal : Format.formatter -> bool -> unit

val pp_spec : Format.formatter -> spec_fct -> unit
val pp_cur_spec : Format.formatter -> unit -> unit

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** {2 Eager} *)

val equiv_eager : string -> AstLogic.equiv -> Ast.stmt * Ast.stmt -> 
  goal * goal



(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
type hl_certif
type hl_spec 

val gen_wp_hl : (Ast.fct -> hl_spec) ->
                (Ast.instr -> Fol.pred) -> 
           Ast.stmt -> Fol.pred -> Fol.pred * hl_certif

