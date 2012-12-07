(* -------------------------------------------------------------------- *)
open EcSymbols
open EcUtils

(* -------------------------------------------------------------------- *)
let qsymb_of_symb (x : symbol) : qsymbol = ([], x)

(* -------------------------------------------------------------------- *)
module Location = struct
  open Lexing

  type t = {
    loc_fname : string;
    loc_start : int * int;
    loc_end   : int * int;
  }

  let dummy = {
    loc_fname = "";
    loc_start = (-1, -1);
    loc_end   = (-1, -1);
  }

  let make (p1 : position) (p2 : position) =
    let mkpos (p : position) =
      (p.pos_lnum, p.pos_cnum - p.pos_bol)
    in
      { loc_fname = p1.pos_fname;
        loc_start = mkpos p1    ;
        loc_end   = mkpos p2    ; }

  let of_lexbuf (lb : lexbuf) =
    let p1 = Lexing.lexeme_start_p lb in
    let p2 = Lexing.lexeme_end_p lb in
      make p1 p2

  let tostring (p : t) =
    Printf.sprintf "%s:%d.%d-%d.%d"
      p.loc_fname
      (fst p.loc_start) (snd p.loc_start)
      (fst p.loc_end  ) (snd p.loc_end  )
end

type 'a located = {
  pl_loc  : Location.t;
  pl_desc : 'a;
}

(* -------------------------------------------------------------------- *)
type side = int

type pty    = pty_r    located          (* located type              *)
and  pexpr  = pexpr_r  located          (* located expression        *)
and  prexpr = prexpr_r located          (* located random expression *)

and pty_r =
  | PTunivar
  | PTtuple     of pty list
  | PTnamed     of qsymbol
  | PTvar       of symbol
  | PTapp       of qsymbol * pty list

and pexpr_r =
  | PEunit                                (* unit literal      *)
  | PEbool   of bool                      (* bool literal      *)
  | PEint    of int                       (* int. literal      *)
  | PEident  of qsymbol                   (* symbol            *)
  | PEapp    of qsymbol * pexpr list      (* op. application   *)
  | PElet    of lpattern * pexpr * pexpr  (* let binding       *)
  | PEtuple  of pexpr list                (* tuple constructor *)
  | PEif     of pexpr * pexpr * pexpr     (* _ ? _ : _         *)
  | PErnd    of prexpr                    (* random expression *)

and prexpr_r =
  | PRbool                                (* flip               *)
  | PRinter    of pexpr * pexpr           (* interval sampling  *)
  | PRbitstr   of pexpr                   (* bitstring sampling *)
  | PRexcepted of prexpr * pexpr          (* restriction        *)
  | PRapp      of qsymbol * pexpr list    (* p-op. application  *)

and lpattern =
  | LPSymbol of symbol
  | LPTuple  of symbol list

type plvalue =
  | PLvSymbol of qsymbol
  | PLvTuple  of qsymbol list
  | PLvMap    of qsymbol * pexpr

type prvalue =
  [`Expr of pexpr | `Call of qsymbol * pexpr list]

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
  | Pty_app   of qsymbol * qsymbol list
  | Pty_func  of (symbol * qsymbol) list * psignature
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
  pfd_uses     : (qsymbol list) option;
}

(* -------------------------------------------------------------------- *)
and pmodule_expr =
  | Pm_ident  of qsymbol * qsymbol list
  | Pm_struct of pstructure

and pstructure = {
  ps_params    : (symbol * qsymbol) list;
  ps_signature : pmodule_type option;
  ps_body      : pstructure_item list;
}

and pstructure_item =
  | Pst_mod   of (symbol * pmodule_expr)
  | Pst_var   of (symbol list * pty)
  | Pst_fun   of (pfunction_decl * pfunction_body)
  | Pst_alias of (symbol * qsymbol)

and pfunction_body = {
  pfb_locals : (symbol list * pty * pexpr option) list;
  pfb_body   : pstmt;
  pfb_return : pexpr option;
}

(* -------------------------------------------------------------------- *)

type poperator = {
  po_name   : symbol;
  po_tyvars : symbol list option;
  po_dom : pty list option;
  po_codom : pty;  
  po_body   : (symbol list * pexpr) option;
  po_prob   : bool;
}

(* -------------------------------------------------------------------- *)
type ptydecl = {
  pty_name   : symbol;
  pty_tyvars : symbol list;
  pty_body   : pty option;
}

(* -------------------------------------------------------------------- *)
type ptylocals = (symbol * pty) list

type pbinop =
  | PPand
  | PPor
  | PPimp
  | PPiff

type pformula = pformula_r located

and pformula_r = 
  | PFunit                                (* unit literal      *)
  | PFbool   of bool                      (* bool literal      *)
  | PFint    of int                       (* int. literal      *)
  | PFtuple  of pformula list                (* tuple *)
  | PFident  of qsymbol                   (* symbol            *)
  | PFside   of pformula * side         
  | PFnot    of pformula 
  | PFbinop  of pformula * pbinop * pformula
  | PFapp    of qsymbol * pformula list
  | PFif     of pformula * pformula * pformula
  | PFlet    of lpattern * pformula * pformula
  | PFforall of ptylocals * pformula
  | PFexists of ptylocals * pformula


(* -------------------------------------------------------------------- *)
type paxiom_kind = PAxiom | PLemma

type paxiom = {
  pa_name    : symbol;
  pa_formula : pformula;
  pa_kind : paxiom_kind;
}

(* -------------------------------------------------------------------- *)
type 'a abstr_def = 
  | AbstrDef of pty list option
  | ConcrDef of ptylocals * 'a 

type ppredicate = {
  pp_name   : symbol;
  pp_tyvars : symbol list option;
  pp_dom    : pty list option;
  pp_body   : (symbol list * pformula) option;
}


(* -------------------------------------------------------------------- *)
type ident_spec = symbol list

type inv = (pformula, (pformula * pformula) * pformula option) EcAstlogic.g_inv

type equiv_concl =
  | Aequiv_spec of (pformula * pformula) * (pexpr * pexpr) option
  | Aequiv_inv  of inv

type auto_info = inv option * ident_spec

type auto_eager = (auto_info, pstmt) EcAstlogic.helper
      
type equiv = {
  eq_name  : symbol           ;
  eq_left  : qsymbol          ;
  eq_right : qsymbol          ;
  eq_concl : equiv_concl      ;
  eq_auto  : auto_eager option;
}

(* -------------------------------------------------------------------- *)
type cnst_decl = (symbol list * pty) * pexpr option

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

type claim = symbol * (pexpr * hint)

(* -------------------------------------------------------------------- *)
type pprint = 
  | Pr_ty of qsymbol
  | Pr_op of qsymbol
  | Pr_th of qsymbol
  | Pr_pr of qsymbol
  | Pr_ax of qsymbol

(* -------------------------------------------------------------------- *)
type global =
  | Gmodule    of (symbol * pmodule_expr)
  | Ginterface of (symbol * pmodule_type)
  | Goperator  of poperator
  | Gpredicate of ppredicate
  | Gaxiom     of paxiom
  | Gclaim     of claim
  | Gtype      of ptydecl
  | Gprint     of pprint
  | GthOpen    of symbol
  | GthClose   of symbol
  | GthRequire of symbol
  | GthImport  of qsymbol

type prog = global list
