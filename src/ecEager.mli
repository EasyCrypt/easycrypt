type eager_trace =
  | ETempty
  | ETcall of int * eager_trace
  | ETif of eager_trace * eager_trace * eager_trace
  | ETwhile of eager_trace * eager_trace


val eq_stmt_name : (Ast.fct -> Ast.fct -> bool) -> Ast.stmt -> Ast.stmt -> bool

val check_sample_stmt : Ast.stmt -> Ast.stmt -> EcTerm.Vset.t * EcTerm.Vset.t
val check_certif : (Ast.fct -> Ast.fct -> int -> bool) ->
  EcTerm.Vset.t -> EcTerm.Vset.t -> Ast.stmt -> Ast.stmt -> eager_trace -> bool
val build_certif : (Ast.fct -> Ast.fct -> int) ->
  EcTerm.Vset.t -> EcTerm.Vset.t -> Ast.stmt -> Ast.stmt -> eager_trace

val find_sample_stmt : Ast.stmt -> Ast.stmt -> Ast.stmt -> Ast.stmt ->
  (Ast.stmt * Ast.stmt * Ast.stmt) * (Ast.stmt * Ast.stmt * Ast.stmt)


val eq_exp_name : Ast.var_exp -> Ast.var_exp -> bool
