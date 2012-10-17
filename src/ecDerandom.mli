
val derandomize_exp : Global.venv -> Ast.lasgn option -> Ast.exp -> 
		      Global.venv * Ast.stmt * Ast.var_exp

val derandomize_stmt : Global.venv -> Ast.stmt -> 
                       Global.venv * Ast.stmt * Ast.stmt

