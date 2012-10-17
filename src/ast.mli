open EcUtil

(* Polymorphic type *)

type native_op =
  (* logical operators *)
  | AND
  | OR
  | XOR
  | IMPL
  | NOT
  (* Arith *)
  | INT_OPP
  | INT_ADD
  | INT_MUL
  | INT_SUB
  | INT_DIV
  | INT_MOD
  | INT_LT
  | INT_LE
  | INT_POW
  | INT_ABS
  (* Equality *)
  | EQ
  (* List *)
  | CONS_LIST
  | APPEND_LIST
  | IN_LIST
  | LENGTH_LIST
  (* Option *)
  | SOME_OPT (* REMOVE ? *)
  (* Map *)
  | PUPD_MAP
  | PGET_MAP
  | PINDOM_MAP
  | PINRNG_MAP
  (* Real *)
  | REAL_OF_INT
  | REAL_OF_BOOL
  | REAL_OPP
  | REAL_ADD
  | REAL_MUL
  | REAL_SUB
  | REAL_DIV
  | REAL_POW
  | REAL_ABS
  | REAL_EXP
  | REAL_LT
  | REAL_LE





(** Type after typing *)

(* Types *)

(* 
 * Beware of the existence of "named" types, and the equivalence 
 * for instance of Tint and Pnamed ("int",...,Tint)
 * ALWAYS use Unification.unify_type
 *)
type type_exp =
  | Tunit | Tbool | Tint | Treal | Tbitstring of cst_exp 
  | Ttuple of type_exp list
  | Tnamed of tdef (* globaly declared type *)
  | Tvar of tvar   (* type variable, used for polymorphism *)

and tvar_def = 
  | Closed               (* Not open to unification *)
  | Open                 (* Open to unification *)
  | Defined of type_exp  (* Unification has been done *)


and tvar = {
  tv_name : string;
  tv_id : UID.tvar;
  tv_pos : pos;
  mutable tv_def : tvar_def;
}

and tdef = {
  t_name : string;
  t_wsymbol : Why3.Ty.tysymbol;
  t_native_why : bool; (* true -> why3 type *)
  t_pos : pos;
  t_poly : type_exp list;
  t_def : type_exp option
}

(* Expressions *)

and ('var, 'c, 'b, 'op, 'e) g_exp =
  | Ecnst of 'c cnst
  | Ebase of 'b
  | Ernd of ('op,'e) g_random
  | Eapp of 'op * 'e list
  | Elet of 'var list * 'e * 'e
  (* TODO : encode this construction using Eapp *)
  | Epair of 'e list
  | Eif of 'e * 'e * 'e

(* Constants *)

and ('op,'e) g_random =
  | Rinter of 'e * 'e
  | Rbool
  | Rbitstr of 'e
  | Rexcepted of ('op,'e) g_random * 'e
  | Rapp of 'op * 'e list

and 'c cnst =
  | Ebool of bool
  | Eint of int
  | Ecst of 'c

and const_body = {
  c_name : string;
  c_poly : tvar list;
  c_type : type_exp;
  c_pos  : pos;
  c_def  : cst_exp option;
  c_why3 : Why3.Decl.logic_decl;
  c_native_why : bool; (* true -> native *)
}

and const = const_body * tvar list

(* Expression with only constants *)

and cst_exp = exp

(* Operators *)

and g_fct_sig = type_exp list * type_exp

and oper = pos * oper_body * tvar list

and oper_body = {
  op_name  : string;
  op_native : native_op option;
  op_why    : string * bool;
  op_why3   : Why3.Decl.logic_decl;
  op_native_why : bool; (* true -> native *)
  op_id    : UID.op;
  op_poly  : tvar list;
  op_type  : g_fct_sig ;
  op_body  : (var list * var_exp) option; (* no random for the moment *)
  op_infix : bool;
  op_pos   : pos;
  op_assoc : bool option;
  op_prec  : int;
}

(* Variables *)
and var = {
  v_name : string;
  v_id   : UID.var;
  v_glob : bool;
  v_type : type_exp;
  v_pos  : pos;
}

(* Expression with constants and variables *)


and var_exp = exp

(* Random *)

and exp = (var, const, var, oper, exp) g_exp

type ('v1, 'v2) v_exp = ('v1, const, 'v2, oper, ('v1,'v2) v_exp) g_exp

type random = (oper,var_exp) g_random

(* Instructions *)

type vars_decl = var list

type adversary =
    { adv_name : string;
      adv_pos : pos;
      adv_param : vars_decl;
      adv_res : type_exp;
      adv_odecl : g_fct_sig list
    }

(*type instr_body = (var, exp, fct, stmt) g_instr
  and instr = { i_pos : pos; i_body : instr_body }
  and stmt = instr list *)

type ('v,'e) g_lasgn =
  | Ltuple of 'v list
  | Lupd of 'v * 'e

type ('l, 'e, 'f, 's) g_instr =
  | Sasgn of 'l * 'e
  | Scall of 'l * 'f * 'e list
  | Sif of 'e * 's * 's
  | Swhile of 'e * 's
  | Sassert of 'e

type lasgn = (var,exp) g_lasgn

type instr = (lasgn, exp, fct, stmt) g_instr

and stmt = instr list

and fct = {
  f_name : string ;
  f_game : game;
  f_pos : pos;
  f_param : vars_decl;
  f_body : fct_body;
  f_res : var;
  f_modify : var list;
  f_read  : var list;
}
and fct_body =
  | FctAdv of adversary * fct list
  | FctDef of fct_def
and fct_def = {
  f_local : vars_decl;
  f_def : stmt;
  f_return : var_exp option;
}
and game = {
  g_name : string;
  g_pos : pos;
  mutable g_vars : (string * var) list;
  mutable g_functions : (string * fct) list;
}


(** {2 Proba } *)

type real_exp = (var, fct * var_exp) v_exp






