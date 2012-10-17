(** Inlining function *)

type cond = int -> Ast.lasgn -> Ast.fct -> Ast.exp list -> bool

type info = (int * Ast.vars_decl) list

val inline : 
  Global.venv -> cond -> Ast.stmt -> info * Global.venv * Ast.stmt

(** TODO move this to EcTerm *)
val as_defined_call_in : string list -> Ast.stmt -> bool

val as_defined_call : Ast.stmt -> bool

val last_pos : Ast.stmt -> int

    
