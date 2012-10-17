


val pr_list_export :  (bool ref * (string * (Ast.var, Ast.fct * Ast.exp) Ast.v_exp * AstLogic.pr_hint)) list ref

val set_Pr : string list -> unit

val unset_Pr : string list -> unit

val check_and_add : bool -> (string -> AstLogic.equiv) ->
  string -> Ast.real_exp -> AstLogic.pr_hint -> unit

val reset : unit -> unit

