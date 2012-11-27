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
  | Punivar
  | Ptuple     of pty list
  | Pnamed     of qsymbol
  | Pvar       of symbol
  | Papp       of qsymbol * pty list

and pexpr =
  | PEunit                                (* unit literal      *)
  | PEbool   of bool                      (* bool literal      *)
  | PEint    of int                       (* int. literal      *)
  | PEident  of qsymbol                   (* symbol            *)
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
  | PRapp      of qsymbol * pexpr list    (* p-op. application  *)

and lpattern =
  | LPSymbol of symbol
  | LPTuple  of symbol list

      (* deriving(Show) *)

type plvalue =
  | PLvSymbol of qsymbol
  | PLvTuple  of qsymbol list
  | PLvMap    of qsymbol * pexpr
      (* deriving(Show) *)

type prvalue =
  [`Expr of pexpr | `Call of qsymbol * pexpr list]
      (* deriving(Show) *)

(* -------------------------------------------------------------------- *)
type pinstr =
  | PSasgn   of plvalue * prvalue
  | PScall   of qsymbol * pexpr list
  | PSif     of pexpr * pstmt * pstmt
  | PSwhile  of pexpr * pstmt
  | PSassert of pexpr

and pstmt = pinstr list

(* -------------------------------------------------------------------- *)
type pmodule_type =
  | Pty_ident of qsymbol
  | Pty_app   of pmodule_type * pmodule_type
  | Pty_func  of (symbol * psignature) * pmodule_type
  | Pty_sig   of psignature

and psignature = psignature_item list

and psignature_item = [
  | `VariableDecl of pvariable_decl
  | `FunctionDecl of pfunction_decl
]

and pvariable_decl = {
  pvd_name : symbol;
  pvd_type : pty;
}

and pfunction_decl = {
  pfd_name     : symbol;
  pfd_tyargs   : (symbol * pty) list;
  pfd_tyresult : pty;
}

(* -------------------------------------------------------------------- *)
and pmodule_expr =
  | Pm_ident  of qsymbol * qsymbol list
  | Pm_struct of pstructure

and pstructure = {
  ps_params    : (symbol * pmodule_type) list;
  ps_signature : pmodule_type option;
  ps_body      : pstructure_item list;
}

and pstructure_item =
  | Pst_mod of (symbol * pmodule_expr)
  | Pst_var of (symbol list * pty)
  | Pst_fun of (pfunction_decl * pfunction_body)

and pfunction_body = {
  pfb_locals : (symbol list * pty * pexpr option) list;
  pfb_body   : pstmt;
  pfb_return : pexpr option;
}

(* -------------------------------------------------------------------- *)
type ptheory_item =
  | Pth_module  of symbol * pmodule_expr
  | Pth_modtype of symbol * pmodule_type

(* -------------------------------------------------------------------- *)
type formula = int

(* -------------------------------------------------------------------- *)
type ident_spec = symbol list

type inv = (formula, (formula * formula) * formula option) AstLogic.g_inv

type equiv_concl = 
  | Aequiv_spec of (formula * formula) * (pexpr * pexpr) option
  | Aequiv_inv  of inv

type auto_info = inv option * ident_spec

type auto_eager = (auto_info, pstmt) AstLogic.helper
      
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
  | Gmodule    of (symbol * pmodule_expr)
  | Ginterface of (symbol * pmodule_type)
  | Gcnst      of cnst_decl
  | Gclaim     of claim
  | Gtype      of (qsymbol * pty option)
      (* deriving (Show) *) 

type prog = global list
