val log2 : int -> int
module Env :
  sig
    type env
    val empty : env
    module Fun :
      sig
        val get : env -> Ast.ident -> Ast.aargs * Ast.aexpr
        val bind : env -> Ast.ident -> Ast.aargs * Ast.aexpr -> env
      end
    module Var :
      sig
        val get : env -> Ast.ident -> Aig.reg
        val bind : env -> Ast.ident -> Aig.reg -> env
        val bindall : env -> (Ast.ident * Aig.reg) list -> env
      end
  end
type env = Env.env
val circuit_of_spec : Aig.reg list -> Ast.adef -> Aig.reg
