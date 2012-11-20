(* -------------------------------------------------------------------- *)
open EcUtil
open EcScope

(* -------------------------------------------------------------------- *)
type 'a context = 'a Context.context

type symbol  = string
type qsymbol = symbol list * symbol

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

type tyexpr =
  | Tunit
  | Tbool
  | Tint
  | Treal
  | Tbitstring of expr
  | Ttuple     of tyexpr list
  | Tnamed     of symbol
  | Tvar       of UID.uid

and expr =
  | Ebool  of bool                      (* bool literal      *)
  | EInt   of int                       (* int. literal      *)
  | Eident of qsymbol                   (* variable          *)
  | Eapp   of symbol * expr list        (* op. application   *)
  | Elet   of lpattern * expr * expr    (* let binding       *)
  | ETuple of expr list                 (* tuple constructor *)
  | Eif    of expr * expr * expr        (* _ ? _ : _         *)
  | Ernd   of rexpr

and rexpr =
  | Rbool                               (* flip               *)
  | Rinter    of expr * expr            (* interval sampling  *)
  | Rbitstr   of expr                   (* bitstring sampling *)
  | Rexcepted of rexpr * expr           (* restriction        *)
  | Rapp      of symbol * expr list     (* p-op. application  *)

and lpattern =
  | LPSymbol of symbol
  | LPTuple  of symbol list

type instr =
  | Sasgn_e of symbol * expr
  | Sasgn_f of symbol * qsymbol * expr list
  | Scall   of qsymbol * expr list
  | Sif     of expr * stmt * stmt
  | Swhile  of expr * stmt
  | Sassert of expr

and stmt = instr list

and function_ = {
  f_name   : string ;
  f_param  : (symbol * tyexpr) list;
  f_body   : function_body;
  f_modify : symbol list;
  f_read   : symbol list;
}

and function_body =
  | Falias of qsymbol
  | Fdef   of function_def

and function_def = {
  f_local  : (symbol * tyexpr) list;
  f_def    : stmt;
  f_return : expr option;
}

and module_item =
  [ `Variable of symbol * tyexpr * expr
  | `Function of function_
  | `Module   of module_
  ]

and module_ = {
  m_name         : symbol;
  m_interface    : [ `Structural of signature | `Named of qsymbol ];
  m_subinterface : symbol option;
  m_context      : module_item context;
}

and signature_item = [ `FunctionDecl of fun_signature ]

and signature = {
  s_context : signature_item context;
}

and fun_signature = {
  if_name   : string;
  if_params : (string * tyexpr) list;
  if_type   : tyexpr;
}

(* -------------------------------------------------------------------- *)
type theory_item =
  [ `Interface  of symbol * signature
  | `ModuleDecl of symbol * signature
  | `Module     of module_
  ]

type theory = {
  th_name : string;
  th_body : theory_item context;
}
