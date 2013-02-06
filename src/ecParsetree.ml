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

(* -------------------------------------------------------------------- *)
type 'a located = {
  pl_loc  : Location.t;
  pl_desc : 'a;
}

let unloc  x = x.pl_desc
let unlocs x = List.map unloc x
let dummyloc x = { pl_loc = Location.dummy; pl_desc = x }
let dummy_pqs_of_ps s = dummyloc (qsymb_of_symb (unloc s))

(* -------------------------------------------------------------------- *)
type side = int

type psymbol  = symbol  located         (* located symbol  *)
 and pqsymbol = qsymbol located         (* located qsymbol *)
type posymbol = symbol option located

type pty = pty_r    located             (* located type *)

and pty_r =
  | PTunivar
  | PTtuple     of pty list
  | PTnamed     of pqsymbol
  | PTvar       of psymbol
  | PTapp       of pqsymbol * pty list
  | PTfun       of pty * pty

type tvar_inst_kind = 
  | TVIunamed of pty list
  | TVInamed  of (psymbol * pty) list

type tvar_inst = tvar_inst_kind option

type pexpr  = pexpr_r located  (* located expression *)

and pexpr_r =
  | PEint      of int                               (* int. literal       *)
  | PEident    of pqsymbol * tvar_inst              (* symbol             *)
  | PEapp      of pexpr * pexpr list                (* op. application    *)
  | PElet      of lpattern * pexpr * pexpr          (* let binding        *)
  | PEtuple    of pexpr list                        (* tuple constructor  *)
  | PEif       of pexpr * pexpr * pexpr             (* _ ? _ : _          *)

and lpattern =
  | LPSymbol of psymbol
  | LPTuple  of psymbol list

type plvalue =
  | PLvSymbol of pqsymbol
  | PLvTuple  of pqsymbol list
  | PLvMap    of pqsymbol * tvar_inst * pexpr

(* -------------------------------------------------------------------- *)
type pinstr =
  | PSasgn   of plvalue * pexpr
  | PSrnd    of plvalue * pexpr
  | PScall   of plvalue option * pqsymbol * pexpr list
  | PSif     of pexpr * pstmt * pstmt
  | PSwhile  of pexpr * pstmt
  | PSassert of pexpr

and pstmt = pinstr list

(* -------------------------------------------------------------------- *)
type pmodule_sig =
| Pmty_alias  of pmodule_type
| Pmty_struct of pmodule_sig_struct

and pmodule_type = pqsymbol * pqsymbol list

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
and pmodule_expr =
  | Pm_ident  of pqsymbol * pqsymbol list
  | Pm_struct of pstructure

and pstructure = {
  ps_params    : (psymbol * pmodule_type) list;
  ps_body      : pstructure_item list;
  ps_signature : pmodule_type list;
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
type poperator = {
  po_name   : psymbol;
  po_tyvars : psymbol list option;
  po_dom    : pty list option;
  po_codom  : pty;  
  po_body   : (psymbol list * pexpr) option;
}

(* -------------------------------------------------------------------- *)
type ptydecl = {
  pty_name   : psymbol;
  pty_tyvars : psymbol list;
  pty_body   : pty option;
}

(* -------------------------------------------------------------------- *)
type ptylocals = (psymbol * pty) list

type pfct_game = pqsymbol

type ptyped_mem = int * pfct_game 

type pformula = pformula_r located

and pformula_r = 
  | PFint    of int                       (* int. literal      *)
  | PFtuple  of pformula list             (* tuple             *)
  | PFident  of pqsymbol * tvar_inst      (* symbol            *)
  | PFside   of pformula * side         
  | PFapp    of pformula * pformula list
  | PFif     of pformula * pformula * pformula
  | PFlet    of lpattern * pformula * pformula
  | PFforall of ptylocals * pformula
  | PFexists of ptylocals * pformula
  (* for claim *)
  | PFforallm of ptyped_mem list * pformula
  | PFexistsm of ptyped_mem list * pformula
  | PFprob    of pfct_game * int * pformula


(* -------------------------------------------------------------------- *)
type paxiom_kind = PAxiom | PLemma | PILemma

type paxiom = {
  pa_name    : psymbol;
  pa_formula : pformula;
  pa_kind : paxiom_kind;
}

(* -------------------------------------------------------------------- *)
type 'a abstr_def = 
  | AbstrDef of pty list option
  | ConcrDef of ptylocals * 'a 

type ppredicate = {
  pp_name   : psymbol;
  pp_tyvars : psymbol list option;
  pp_dom    : pty list option;
  pp_body   : (psymbol list * pformula) option;
}

(* -------------------------------------------------------------------- *)
(* -------------------------------------------------------------------- *)
type pprover_infos = 
  int option * string located list option

type elim_kind = 
  | ElimHyp  of pqsymbol * tvar_inst
  | ElimForm of pformula

type pelim = 
  { elim_kind : elim_kind;
    elim_args : pformula option list }

type ptactic = ptactic_r located

and ptactic_r = 
  | Pidtac
  | Passumption of (pqsymbol option * tvar_inst)
  | Ptrivial    of pprover_infos
  | Pintro      of posymbol list  (* imp_I, forall_I *)
  | Psplit                        (* and_I *)
  | Pexists     of pformula list  (* exists_I *)
  | Pleft                         (* or_I left *)
  | Pright                        (* or_I right *)
  | Pelim       of pelim   
  | Papply      of pelim
  | Psubgoal    of ptactics
  | Pseq        of ptactics

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
| PTHO_Type   of pty
| PTHO_Module of pqsymbol * (pqsymbol list)

(* -------------------------------------------------------------------- *)
type global =
  | Gmodule      of (psymbol * pmodule_expr)
  | Ginterface   of (psymbol * pmodule_sig)
  | Goperator    of poperator
  | Gpredicate   of ppredicate
  | Gaxiom       of paxiom
  | Gclaim       of claim
  | Gtype        of ptydecl
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
  | Gsave

type prog =
  | P_Prog of global list * bool
  | P_Undo of int
