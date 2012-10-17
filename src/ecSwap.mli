exception CanNotSwap of string

val independent : Ast.stmt -> Ast.stmt -> bool

val pg_swap_fct : AstLogic.swap_kind -> Ast.instr list -> Ast.instr list 

