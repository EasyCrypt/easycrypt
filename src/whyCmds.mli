
val set_prover_option : string list -> unit

val check_why3 : 
      ?timeout:int -> ?pp_failure:bool -> ?goal_name:string -> Fol.pred -> bool

val check_implies : Fol.pred -> Fol.pred -> bool

val prove: Fol.pred -> bool

val simplify_post : bool -> Fol.pred -> Fol.pred -> Fol.pred 

val check_pr : string ->
  (bool ref * (string * (Ast.var, Ast.fct * Ast.exp) Ast.v_exp)) list ->
  Ast.real_exp -> bool

val check_computed_pr : string ->
  (bool ref * (string * (Ast.var, Ast.fct * Ast.exp) Ast.v_exp)) list ->
  ((Ast.exp * Ast.exp) list * Ast.exp) -> bool -> Ast.real_exp -> bool

val my_check_computed_pr_cond : string -> 
  Ast.exp list ->
    (Ast.exp * Ast.exp) list -> 
      Ast.exp -> bool

val check_computed_pr_cond : string ->
  (bool ref * (string * (Ast.var, Ast.fct * Ast.exp) Ast.v_exp)) list ->
  Ast.exp list ->
  ((Ast.exp * Ast.exp) list * Ast.exp) -> bool -> Ast.real_exp -> bool

