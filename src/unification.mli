open EcUtil
open Ast

exception TypeMismatch of type_exp * type_exp

val unify_type : type_exp -> type_exp -> unit

val unify_type_list : type_exp list -> type_exp list -> unit

val raise_unify_type : type_exp -> type_exp -> pos -> string -> unit

val eq_type : type_exp -> type_exp -> bool



