type env

val empty  : env

type rebinding_item
type rebinding = rebinding_item list

val rebind : env -> rebinding -> env

(* importing why3 theory *)

type renaming_kind =
  | RDts 
  | RDls
  | RDpr

type renaming_decl = (string list * renaming_kind * EcIdent.t) list

val import_w3 : 
    env -> EcPath.path -> 
      Why3.Theory.theory -> 
        renaming_decl -> EcTypesmod.theory * rebinding_item 

val add_ty : env -> EcPath.path -> EcDecl.tydecl -> env * rebinding_item

val add_op : 
    env -> EcPath.path -> EcDecl.operator -> env * rebinding_item option

val add_ax : env -> EcPath.path -> EcDecl.axiom -> env * rebinding_item

val get_w3_th : string list -> string -> Why3.Theory.theory
  
