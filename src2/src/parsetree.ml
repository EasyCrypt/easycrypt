(* -------------------------------------------------------------------- *)
open Symbols
open Utils

type side    = [ `Left | `Right ]    (* deriving(Show) *)

let qsymb_of_symb (x : symbol) : qsymbol = ([], x)

type tyexpr =
  | Punit
  | Pbool
  | Pint
  | Preal
  | Pbitstring of expr
  | Ptuple     of tyexpr list
  | Pnamed     of symbol
  | Pvar       of symbol
  | Papp       of symbol * tyexpr list

and expr =
  | PEunit                                (* unit literal      *)
  | PEbool   of bool                      (* bool literal      *)
  | PEint    of int                       (* int. literal      *)
  | PElist   of expr list                 (* list literal      *)
  | PEident  of qsymbol                   (* symbol            *)
  | PErelvar of symbol * side             (* rel. variable     *)
  | PEapp    of qsymbol * expr list       (* op. application   *)
  | PElet    of lpattern * expr * expr    (* let binding       *)
  | PEtuple  of expr list                 (* tuple constructor *)
  | PEif     of expr * expr * expr        (* _ ? _ : _         *)
  | PErnd    of rexpr                     (* random expression *)

and rexpr =
  | PRbool                                (* flip               *)
  | PRinter    of expr * expr             (* interval sampling  *)
  | PRbitstr   of expr                    (* bitstring sampling *)
  | PRexcepted of rexpr * expr            (* restriction        *)
  | PRapp      of symbol * expr list      (* p-op. application  *)

and lpattern =
  | LPSymbol of symbol
  | LPTuple  of symbol list

      (* deriving(Show) *)

type lvalue =
  | LVSymbol of qsymbol
  | LVTuple  of qsymbol list
  | LVMap    of qsymbol * expr
      (* deriving(Show) *)

type rvalue =
  [`Expr of expr | `Call of qsymbol * expr list]
      (* deriving(Show) *)

type instr =
  | Sasgn   of lvalue * rvalue
  | Scall   of qsymbol * expr list
  | Sif     of expr * stmt * stmt
  | Swhile  of expr * stmt
  | Sassert of expr

and stmt = instr list

and function_decl = {
  fd_name     : symbol;
  fd_tyargs   : (symbol * tyexpr) list;
  fd_tyresult : tyexpr;
}

and function_body = {
  fb_locals : (symbol list * tyexpr * expr option) list;
  fb_body   : stmt;
  fb_return : expr option;
}

and module_item =
  | PEVar   of (symbol list * tyexpr)
  | PEFun   of (function_decl * function_body)
  | PERedef of (symbol * qsymbol)
  | PEMod   of module_

and module_ = {
  m_name         : symbol;
  m_subinterface : symbol option;
  m_body         : module_item list;
}

and signature_item = [ `FunctionDecl of function_decl ]

and signature = {
  s_context : signature_item list;
}

and interface = {
  i_name      : symbol;
  i_signature : signature;
}
    (* deriving(Show) *)

(* -------------------------------------------------------------------- *)
type formula = int

(* -------------------------------------------------------------------- *)
type ident_spec = symbol list

type inv = (formula, (formula * formula) * formula option) AstLogic.g_inv

type equiv_concl = 
  | Aequiv_spec of (formula * formula) * (expr * expr) option
  | Aequiv_inv  of inv

type auto_info = inv option * ident_spec

type auto_eager = (auto_info, stmt) AstLogic.helper
      
type equiv = {
  eq_name  : symbol           ;
  eq_left  : qsymbol          ;
  eq_right : qsymbol          ;
  eq_concl : equiv_concl      ;
  eq_auto  : auto_eager option;
}

(* -------------------------------------------------------------------- *)
type cnst_decl = (symbol list * tyexpr) * expr option
    (* deriving(Show) *)

(* -------------------------------------------------------------------- *)
type hint =
  | Husing of symbol
  | Hadmit
  | Hcompute
  | Hnone
  | Hsame
  | Hsplit
  | Hauto
  | Hfailure of int * expr * expr * (symbol * expr) list

      (* deriving(Show) *)

type claim = symbol * (expr * hint)
    (* deriving(Show) *)

(* -------------------------------------------------------------------- *)
type global =
  | Gmodule    of module_
  | Ginterface of interface
  | Gcnst      of cnst_decl
  | Gclaim     of claim
  | Gtype      of (qsymbol * tyexpr option)
      (* deriving (Show) *) 

type prog = global list
