
val open_equiv : string -> AstLogic.equiv -> unit

(* App *)
val app_tac : int*int -> AstYacc.p_fol -> 
  (AstYacc.p_exp * AstYacc.p_exp * AstYacc.p_exp * AstYacc.p_exp) option
  -> EcDeriv.tactic

(* Call *)
val wp_call_tac : AstYacc.auto_info -> EcDeriv.tactic 

(* reduce branching *)
val ifsync_tac :  (int * int) option -> EcDeriv.tactic
val ifneg_tac :  ApiTypes.side * AstLogic.at_pos -> EcDeriv.tactic
val reduce_cond_tac : (ApiTypes.side * AstLogic.at_pos * bool) -> EcDeriv.tactic

val unroll_tac : (ApiTypes.side * AstLogic.at_pos) -> EcDeriv.tactic

(* Inlining *)
val inline_tac :  string list AstLogic.inline_info -> EcDeriv.tactic

(* Derandomize *)
val derandomize_tac : ApiTypes.side -> EcDeriv.tactic

(* Trivial *)
val prove_tac : EcDeriv.tactic
val trivial_tac : EcDeriv.tactic

(* Auto *)

val auto_tac : AstYacc.auto_info -> EcDeriv.tactic

(* Sort *)
val sort_tac : ApiTypes.side -> EcDeriv.tactic

val set_tac :
    ApiTypes.side * AstLogic.at_pos * AstYacc.p_var *
    AstYacc.type_exp * AstYacc.p_exp -> EcDeriv.tactic

(* auto_rnd *)

val auto_rnd_tac : EcDeriv.tactic

(* rnd tac *)
val rnd_tac : AstLogic.tac_direction * (string option * AstYacc.p_exp) AstLogic.rnd_info -> EcDeriv.tactic


val while_tac :  
    ApiTypes.side * AstLogic.tac_direction * AstYacc.p_fol *
      (AstYacc.p_exp * AstYacc.p_exp) option -> EcDeriv.tactic

val splitwhile_tac : 
    ApiTypes.side * AstLogic.at_pos * AstYacc.p_exp ->
      EcDeriv.tactic

(* TODO: remove this *)
(* gen_wp_fct_body *)
val gen_wp_fct_body : (Ast.fct -> Ast.fct -> EcDeriv.tactic) -> EcDeriv.tactic

(* build automaticaly equiv *)
val equiv_fct :
    ?find:bool ->
    ?name:string option ->
      FunLogic.inv * string list ->
        Ast.fct -> Ast.fct -> Fol.pred -> Fol.pred -> EcDeriv.spec_fct

val equiv_inv_fct : 
    ?name:string option ->
      FunLogic.inv * string list ->
        Ast.fct -> Ast.fct -> EcDeriv.spec_fct

val eager : string -> AstLogic.equiv -> Ast.stmt * Ast.stmt -> unit 

val proba : bool -> string -> AstLogic.claim -> unit   

val autosync_tac :  EcDeriv.tactic

val eqobs_in_tac : 
    AstYacc.p_exp -> AstYacc.p_exp -> AstYacc.p_exp -> string list -> EcDeriv.tactic

