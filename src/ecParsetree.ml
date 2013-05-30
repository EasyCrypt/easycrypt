(* -------------------------------------------------------------------- *)
open EcSymbols
open EcLocation
open EcUtils

(* -------------------------------------------------------------------- *)
exception ParseError of EcLocation.t * string option

let pp_parse_error fmt msg =
  match msg with
  | Some msg -> Format.fprintf fmt "parse error: %s" msg
  | None     -> Format.fprintf fmt "parse error"

let () =
  let pp fmt exn =
    match exn with
    | ParseError (_loc, msg) -> pp_parse_error fmt msg
    | _ -> raise exn
  in
    EcPException.register pp

(* -------------------------------------------------------------------- *)
let qsymb_of_symb (x : symbol) : qsymbol = ([], x)

(* -------------------------------------------------------------------- *)
type psymbol  = symbol  located
type pqsymbol = qsymbol located

type pmsymbol = (psymbol * ((pmsymbol located) list) option) list

(* -------------------------------------------------------------------- *)
type pty_r =
  | PTunivar
  | PTtuple     of pty list
  | PTnamed     of pqsymbol
  | PTvar       of psymbol
  | PTapp       of pqsymbol * pty list
  | PTfun       of pty * pty
and pty       = pty_r       located

type ptyannot_r = 
  | TVIunamed of pty list
  | TVInamed  of (psymbol * pty) list
and ptyannot  = ptyannot_r  located

type plpattern_r =
  | LPSymbol of psymbol
  | LPTuple  of psymbol list
and plpattern = plpattern_r located


type ptybinding  = psymbol list * pty
and ptybindings = ptybinding list

and pexpr_r =
  | PEint      of int                               (* int. literal       *)
  | PEident    of pqsymbol * ptyannot option        (* symbol             *)
  | PEapp      of pexpr * pexpr list                (* op. application    *)
  | PElet      of plpattern * pexpr * pexpr         (* let binding        *)
  | PEtuple    of pexpr list                        (* tuple constructor  *)
  | PEif       of pexpr * pexpr * pexpr             (* _ ? _ : _          *)
  | PElambda   of ptybindings * pexpr
and pexpr     = pexpr_r     located

(* -------------------------------------------------------------------- *)

type plvalue_r =
  | PLvSymbol of pqsymbol
  | PLvTuple  of pqsymbol list
  | PLvMap    of pqsymbol * ptyannot option * pexpr
and plvalue   = plvalue_r   located

type pinstr =
  | PSasgn   of plvalue * pexpr
  | PSrnd    of plvalue * pexpr
  | PScall   of plvalue option * pqsymbol * pexpr list
  | PSif     of pexpr * pstmt * pstmt
  | PSwhile  of pexpr * pstmt
  | PSassert of pexpr

and pstmt = pinstr list

(* -------------------------------------------------------------------- *)
type pmodule_type = pqsymbol 

and pmodule_sig =
  | Pmty_struct of pmodule_sig_struct

and pmodule_sig_struct = {
  pmsig_params : (psymbol * pmodule_type) list;
  pmsig_body   : pmodule_sig_struct_body;
}

and pmodule_sig_struct_body = pmodule_sig_item list

and pmodule_sig_item = [
  | `VariableDecl of pvariable_decl
  | `FunctionDecl of pfunction_decl
]

and pvariable_decl = {
  pvd_name : psymbol;
  pvd_type : pty;
}

and pfunction_decl = {
  pfd_name     : psymbol;
  pfd_tyargs   : (psymbol * pty) list;
  pfd_tyresult : pty;
  pfd_uses     : (pqsymbol list) option;
}

(* -------------------------------------------------------------------- *)
and pmodule_expr_r =
  | Pm_ident  of pmsymbol
  | Pm_struct of pstructure

and pmodule_expr = pmodule_expr_r located

and pstructure = {
  ps_params    : (psymbol * pmodule_type) list;
  ps_body      : pstructure_item list;
  ps_signature : ((pqsymbol * psymbol list) located) list;
}

and pstructure_item =
  | Pst_mod   of (psymbol * pmodule_expr)
  | Pst_var   of (psymbol list * pty)
  | Pst_fun   of (pfunction_decl * pfunction_body)
  | Pst_alias of (psymbol * pqsymbol)

and pfunction_body = {
  pfb_locals : (psymbol list * pty * pexpr option) list;
  pfb_body   : pstmt;
  pfb_return : pexpr option;
}

(* -------------------------------------------------------------------- *)
type ptydecl = {
  pty_name   : psymbol;
  pty_tyvars : psymbol list;
  pty_body   : pty option;
}

(* -------------------------------------------------------------------- *)
type pdatatype = {
  ptd_name   : psymbol;
  ptd_tyvars : psymbol list;
  ptd_ctors  : (psymbol * pty option) list;
}

(* -------------------------------------------------------------------- *)
type pmodule_type_restr = pqsymbol * pmsymbol located list

type pgamepath = (pmsymbol * psymbol) located
type pmemory   = psymbol

type phoarecmp = PFHle | PFHeq | PFHge

type pformula  = pformula_r located

and pformula_r = 
  | PFint    of int
  | PFtuple  of pformula list
  | PFident  of pqsymbol * ptyannot option
  | PFside   of pformula * (int * symbol) located
  | PFapp    of pformula * pformula list
  | PFif     of pformula * pformula * pformula
  | PFlet    of plpattern * pformula * pformula
  | PFforall of pgtybindings * pformula
  | PFexists of pgtybindings * pformula
  | PFlambda of ptybindings * pformula
  | PFglob   of pmsymbol located 

  (* for claims *)
  | PFhoareS   of pformula * pfunction_body * pformula
  | PFhoareF   of pformula * pgamepath * pformula
  | PFequivF   of pformula * (pgamepath * pgamepath) * pformula
  | PFprob     of pgamepath * (pformula list) * pmemory * pformula
  | PFBDhoareS of pformula * pfunction_body * pformula * phoarecmp * pformula
  | PFBDhoareF of pformula * pgamepath * pformula * phoarecmp * pformula

and pgtybinding  = psymbol list * pgty
and pgtybindings = pgtybinding list

and pgty =
| PGTY_Type  of pty
| PGTY_ModTy of pmodule_type_restr
| PGTY_Mem

(* -------------------------------------------------------------------- *)

type pop_def =
  | POabstr of pty
  | POconcr of ptybindings * pty * pexpr

type poperator = {
  po_name   : psymbol;
  po_tyvars : psymbol list option;
  po_def    : pop_def
}

type ppred_def = 
  | PPabstr of pty list
  | PPconcr of ptybindings * pformula  

type ppredicate = {
  pp_name   : psymbol;
  pp_tyvars : psymbol list option;
  pp_def    : ppred_def;
}


(* -------------------------------------------------------------------- *)
type paxiom_kind = PAxiom | PLemma | PILemma

type paxiom = {
  pa_name    : psymbol;
  pa_formula : pformula;
  pa_kind : paxiom_kind;
}

(* -------------------------------------------------------------------- *)
type pprover_infos = {
  pprov_max : int option;
  pprov_time : int option;
  pprov_names : string located list option
}

let empty_pprover = {
  pprov_max   = None;
  pprov_time  = None;
  pprov_names = None;
}

type 'a fpattern_kind = 
  | FPNamed of pqsymbol * ptyannot option
  | FPCut   of 'a 

type fpattern_arg = 
  | EA_form of pformula
  | EA_mem  of pmemory
  | EA_mp   of pmsymbol
  | EA_none 

type 'a fpattern = { 
  fp_kind : 'a fpattern_kind;
  fp_args : fpattern_arg located list 
}

type ffpattern = pformula fpattern

type cfpattern = (pformula option * pformula option) fpattern

type preduction = {
  pbeta   : bool;
  pdelta  : pqsymbol list option;
  pzeta   : bool;   (* remove let *)
  piota   : bool;   (* remove case *)
  plogic  : bool;   (* perform logical simplification *)
  pmodpath : bool;   (* normalize modpath *)
}

(* -------------------------------------------------------------------- *)
type 'a doption = 
  | Single of 'a
  | Double of 'a * 'a

type 'a rnd_tac_info = ('a option) * ('a option)

type tac_side = bool option

type swap_kind = 
  | SKbase      of int * int * int
  | SKmove      of int
  | SKmovei     of int * int
  | SKmoveinter of int * int * int 

type pipattern =
  | PtAny
  | PtAsgn  of psymbol list
  | PtIf    of pspattern * [`NoElse | `MaybeElse | `Else of pspattern]
  | PtWhile of pspattern

and pspattern = unit

type ptactic = ptactic_r located

and ptactic_r = 
  | Pidtac      of string option
  | Prepeat     of ptactic  
  | Pdo         of int option * ptactic (* None means do 1 then repeat *)
  | Ptry        of ptactic 
  | Passumption of (pqsymbol option * ptyannot option)
  | Ptrivial    of pprover_infos
  | Pintro      of (symbol option) located list
  | Psplit                        
  | Pexists     of fpattern_arg located list 
  | Pleft                         
  | Pright                        
  | Pelim       of ffpattern 
  | Papply      of ffpattern
  | Pcut        of (psymbol * pformula)
  | Pgeneralize of pformula list
  | Pclear      of psymbol list
  | Prewrite    of (bool * ffpattern)
  | Psubst      of psymbol list
  | Psimplify   of preduction 
  | Pchange     of pformula
  | PelimT      of (pformula * pqsymbol)
  | Pcase       of pformula 
  | Psubgoal    of ptactics
  | Pseq        of ptactics
  | PPhl        of phl_tactics
  | Padmit
  | Pfield		of (pformula * pformula * pformula * pformula * pformula * pformula * pformula)
  | Pdebug

and phl_tactics = 
  | Pfun_def  
  | Pfun_abs    of pformula
  | Pfun_upto   of (pformula * pformula * pformula option)
  | Pskip
  | Papp        of (int doption * pformula)
  | Pwp         of int doption option 
  | Pwhile      of pformula
  | Pcall       of tac_side * (pformula * pformula)
  | Prcond      of (bool option * bool * int)
  | Pcond       of tac_side
  | Pswap       of ((tac_side * swap_kind) located list)
  | Pinline     of pinline_arg
  | Prnd        of tac_side * pformula rnd_tac_info
  | Pconseq     of cfpattern
  | Pequivdeno  of cfpattern

and pinline_arg =
  [ `ByName    of tac_side * (pgamepath list * int list option)
  | `ByPattern of pipattern ]

and ptactics = ptactic list        

(* -------------------------------------------------------------------- *)
type ident_spec = psymbol list

type inv = (pformula, (pformula * pformula) * pformula option) EcAstlogic.g_inv

type equiv_concl =
  | Aequiv_spec of (pformula * pformula) * (pexpr * pexpr) option
  | Aequiv_inv  of inv

type auto_info = inv option * ident_spec

type auto_eager = (auto_info, pstmt) EcAstlogic.helper
      
type equiv = {
  eq_name  : psymbol          ;
  eq_left  : pqsymbol         ;
  eq_right : pqsymbol         ;
  eq_concl : equiv_concl      ;
  eq_auto  : auto_eager option;
}

(* -------------------------------------------------------------------- *)
type cnst_decl = (psymbol list * pty) * pexpr option

(* -------------------------------------------------------------------- *)
type hint =
  | Husing of psymbol
  | Hadmit
  | Hcompute
  | Hnone
  | Hsame
  | Hsplit
  | Hauto
  | Hfailure of int * pexpr * pexpr * (psymbol * pexpr) list

type claim = psymbol * (pexpr * hint)

(* -------------------------------------------------------------------- *)
type pprint = 
  | Pr_ty of pqsymbol
  | Pr_op of pqsymbol
  | Pr_th of pqsymbol
  | Pr_pr of pqsymbol
  | Pr_ax of pqsymbol

(* -------------------------------------------------------------------- *)
type renaming_kind = 
  | RNty
  | RNop
  | RNpr

type w3_renaming = 
    string list * renaming_kind * string 
    
(* -------------------------------------------------------------------- *)
type theory_cloning = {
  pthc_base : pqsymbol;
  pthc_name : psymbol option;
  pthc_ext  : (psymbol * theory_override) list;
}

and theory_override =
| PTHO_Type of ty_override
| PTHO_Op   of op_override
| PTHO_Pred of pr_override

and ty_override = psymbol list * pty

and op_override = {
  opov_tyvars : psymbol list option;
  opov_args   : ptybinding list;
  opov_retty  : pty;
  opov_body   : pexpr;
}

and pr_override = {
  prov_tyvars : psymbol list option;
  prov_args   : ptybinding list;
  prov_body   : pformula;
}

(* -------------------------------------------------------------------- *)
type global =
  | Gmodule      of (psymbol * pmodule_expr)
  | Ginterface   of (psymbol * pmodule_sig)
  | Goperator    of poperator
  | Gpredicate   of ppredicate
  | Gaxiom       of paxiom
  | Gclaim       of claim
  | Gtype        of ptydecl
  | Gdatatype    of pdatatype
  | Gprint       of pprint
  | GthOpen      of psymbol
  | GthClose     of psymbol
  | GthRequire   of (psymbol * bool option) (* true = export, false = import *)
  | GthImport    of pqsymbol
  | GthExport    of pqsymbol
  | GthClone     of theory_cloning
  | GthW3        of (string list * string * w3_renaming list)
  | Gtactics     of ptactics
  | Gprover_info of pprover_infos
  | Gcheckproof  of bool
  | Gsave        of EcLocation.t
  | Gpragma      of psymbol

type prog =
  | P_Prog of (global located) list * bool
  | P_Undo of int
