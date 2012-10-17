(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
(** Type checking :
    transform {!AstYacc} which is the parser result into {!Ast}
*)
(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)

(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
(** {2 Program } *)

(*
(** compare that all the names exist in both env *)
  val eq_env : venv -> venv -> bool

  val iter : (string -> Ast.var -> unit) -> venv -> unit
*)

val mk_type_exp : EcUtil.pos -> AstYacc.type_exp -> Ast.type_exp
val mk_poly_type_exp : 
    EcUtil.pos -> AstYacc.type_exp -> Ast.tvar list * Ast.type_exp
val mk_type_def : EcUtil.pos -> 
  string list -> string -> AstYacc.type_exp option -> Ast.tdef

val mk_cst_def: Ast.tvar list -> Ast.type_exp -> AstYacc.p_exp -> Ast.exp

val mk_op_sig : EcUtil.pos -> 
  (AstYacc.type_exp list * AstYacc.type_exp) -> Ast.g_fct_sig 

val mk_op_def : EcUtil.pos ->
  AstYacc.param_list -> AstYacc. p_exp ->
    Ast.g_fct_sig * (Ast.var list * Ast.var_exp)

val mk_pop_def : EcUtil.pos ->
  AstYacc.param_list -> AstYacc.p_var * AstYacc.type_exp -> AstYacc.p_exp ->
    Ast.g_fct_sig * (Ast.var list * Ast.var_exp)


val mk_var_exp : Global.venv -> AstYacc.p_exp -> Ast.exp * Ast.type_exp
val mk_var2_exp : Global.lvenv -> Global.venv -> Global.venv -> AstYacc.p_exp 
  -> Fol.term * Ast.type_exp
val mk_rnd_exp : Global.venv -> AstYacc.p_exp -> Ast.exp * Ast.type_exp

val mk_rnd_info: 
  Global.venv -> Global.venv -> 
  string option * Ast.type_exp ->
  (string option * AstYacc.p_exp) AstLogic.rnd_bij_info ->
  (Fol.lvar * Fol.term) AstLogic.rnd_bij_info

val mk_ifct: AstYacc.fun_decl -> Ast.ifct

val mk_fct: Ast.game -> EcUtil.pos ->
  AstYacc.fun_decl -> AstYacc.fun_def_body ->
  EcUtil.pos * string * Ast.var list * Ast.type_exp * Ast.fct_body

val mk_adv_decl : EcUtil.pos -> AstYacc.adv_decl -> Ast.adversary

val mk_adv_body : EcUtil.pos -> Ast.adversary -> string list -> Ast.fct_body

(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
(** {2 Properties } *)


(** TODO: doc ??? AskB. *)
val mk_info : Ast.fct -> Ast.fct -> AstYacc.auto_info -> AstLogic.inv

val mk_claim : EcUtil.pos -> (AstYacc.p_exp * AstYacc.hint) -> AstLogic.claim

val mk_axiom: AstYacc.p_fol -> Fol.pred

val mk_equiv : 
    EcUtil.pos -> 
      AstYacc.qualif_fct_name -> AstYacc.qualif_fct_name ->
        AstYacc.equiv_concl -> AstLogic.equiv

val mk_eager : Ast.fct -> Ast.fct -> AstYacc.stmt -> Ast.stmt * Ast.stmt

val mk_pred : Global.venv -> Global.venv -> AstYacc.p_fol -> Fol.pred

val check_pre : Ast.fct -> Ast.fct -> Fol.pred -> unit
val check_post : Ast.fct -> Ast.fct -> Fol.pred -> unit
(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)

val mk_popspec : AstYacc.pop_spec -> Fol.pop_spec

val mk_pop_aspec : AstYacc.pop_aspec -> Fol.pop_aspec


val mk_predicate : 
  (AstYacc.p_var * AstYacc.type_exp) list -> AstYacc.p_fol ->
  Fol.lvar list * Fol.pred

val mk_apredicate :
  EcUtil.pos * AstYacc.type_exp list -> Ast.type_exp list

val mkeq_globals : Ast.fct -> Ast.fct -> Fol.pred

(* -------------------------------------------------------------------- *)
val interface_match : Ast.game -> Ast.game_interface_body -> bool
