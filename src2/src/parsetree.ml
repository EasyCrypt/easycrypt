(* -------------------------------------------------------------------- *)
open Symbols
open Utils

type side    = [ `Left | `Right ]    (* deriving(Show) *)

let qsymb_of_symb (x : symbol) : qsymbol = ([], x)

type pty =
  | Punit
  | Pbool
  | Pint
  | Preal
  | Pbitstring
  | Ptuple     of pty list
  | Pnamed     of qsymbol
  | Pvar       of symbol
  | Papp       of qsymbol * pty list

and pexpr =
  | PEunit                                (* unit literal      *)
  | PEbool   of bool                      (* bool literal      *)
  | PEint    of int                       (* int. literal      *)
  | PEident  of qsymbol                   (* symbol            *)
  | PErelvar of symbol * side             (* rel. variable     *)
  | PEapp    of qsymbol * pexpr list      (* op. application   *)
  | PElet    of lpattern * pexpr * pexpr  (* let binding       *)
  | PEtuple  of pexpr list                (* tuple constructor *)
  | PEif     of pexpr * pexpr * pexpr     (* _ ? _ : _         *)
  | PErnd    of prexpr                    (* random expression *)

and prexpr =
  | PRbool                                (* flip               *)
  | PRinter    of pexpr * pexpr           (* interval sampling  *)
  | PRbitstr   of pexpr                   (* bitstring sampling *)
  | PRexcepted of prexpr * pexpr          (* restriction        *)
  | PRapp      of symbol * pexpr list     (* p-op. application  *)

and lpattern =
  | LPSymbol of symbol
  | LPTuple  of symbol list

      (* deriving(Show) *)

type lvalue =
  | LVSymbol of qsymbol
  | LVTuple  of qsymbol list
  | LVMap    of qsymbol * pexpr
      (* deriving(Show) *)

type rvalue =
  [`Expr of pexpr | `Call of qsymbol * pexpr list]
      (* deriving(Show) *)

type instr =
  | Sasgn   of lvalue * rvalue
  | Scall   of qsymbol * pexpr list
  | Sif     of pexpr * stmt * stmt
  | Swhile  of pexpr * stmt
  | Sassert of pexpr

and stmt = instr list

and function_decl = {
  fd_name     : symbol;
  fd_tyargs   : (symbol * pty) list;
  fd_tyresult : pty;
}

and function_body = {
  fb_locals : (symbol list * pty * pexpr option) list;
  fb_body   : stmt;
  fb_return : pexpr option;
}

and module_item =
  | PEVar   of (symbol list * pty)
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
  | Aequiv_spec of (formula * formula) * (pexpr * pexpr) option
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
type cnst_decl = (symbol list * pty) * pexpr option
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
  | Hfailure of int * pexpr * pexpr * (symbol * pexpr) list

      (* deriving(Show) *)

type claim = symbol * (pexpr * hint)
    (* deriving(Show) *)

(* -------------------------------------------------------------------- *)
type global =
  | Gmodule    of module_
  | Ginterface of interface
  | Gcnst      of cnst_decl
  | Gclaim     of claim
  | Gtype      of (qsymbol * pty option)
      (* deriving (Show) *) 

type prog = global list
