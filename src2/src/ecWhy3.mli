type env

val add_ty : env -> EcPath.path -> EcDecl.tydecl -> env
val add_op : env -> EcPath.path -> EcDecl.operator -> env
val add_ax : env -> EcPath.path -> EcDecl.axiom -> env
