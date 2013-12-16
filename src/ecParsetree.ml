(* -------------------------------------------------------------------- *)
open EcMaps
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
type psymbol   = symbol  located
type pqsymbol  = qsymbol located
type pmsymbol  = (psymbol * ((pmsymbol located) list) option) list
type pgamepath = (pmsymbol * psymbol) located

(* -------------------------------------------------------------------- *)
type pty_r =
  | PTunivar
  | PTtuple  of pty list
  | PTnamed  of pqsymbol
  | PTvar    of psymbol
  | PTapp    of pqsymbol * pty list
  | PTfun    of pty * pty
  | PTglob   of pmsymbol located
and pty = pty_r located

type ptyannot_r = 
  | TVIunamed of pty list
  | TVInamed  of (psymbol * pty) list
and ptyannot  = ptyannot_r  located

type plpattern_r =
  | LPSymbol of psymbol
  | LPTuple  of psymbol list
  | LPRecord of (pqsymbol * psymbol) list

and plpattern = plpattern_r located

type ptybinding  = psymbol list * pty
and  ptybindings = ptybinding list

and pexpr_r =
  | PEint    of int                               (* int. literal       *)
  | PEident  of pqsymbol * ptyannot option        (* symbol             *)
  | PEapp    of pexpr * pexpr list                (* op. application    *)
  | PElet    of plpattern * pexpr * pexpr         (* let binding        *)
  | PEtuple  of pexpr list                        (* tuple constructor  *)
  | PEif     of pexpr * pexpr * pexpr             (* _ ? _ : _          *)
  | PElambda of ptybindings * pexpr               (* lambda abstraction *)
  | PErecord of pexpr rfield list                 (* record             *)
  | PEproj   of pexpr * pqsymbol                  (* projection         *)
  | PEproji  of pexpr * int                       (* tuple projection   *)
  | PEscope  of pqsymbol * pexpr                  (* scope selection    *)

and pexpr = pexpr_r located

and 'a rfield = {
  rf_name  : pqsymbol;
  rf_tvi   : ptyannot option;
  rf_value : 'a;
}

(* -------------------------------------------------------------------- *)
type plvalue_r =
  | PLvSymbol of pqsymbol
  | PLvTuple  of pqsymbol list
  | PLvMap    of pqsymbol * ptyannot option * pexpr

and plvalue = plvalue_r located

type pinstr_r =
  | PSasgn   of plvalue * pexpr
  | PSrnd    of plvalue * pexpr
  | PScall   of plvalue option * pqsymbol * (pexpr list) located
  | PSif     of pexpr * pstmt * pstmt
  | PSwhile  of pexpr * pstmt
  | PSassert of pexpr

and pinstr = pinstr_r located
and pstmt  = pinstr list

(* -------------------------------------------------------------------- *)
type pmodule_type = pqsymbol 
type pmodule_type_restr = pqsymbol * pmsymbol located list

type pmodule_sig =
  | Pmty_struct of pmodule_sig_struct

and pmodule_sig_struct = {
  pmsig_params : (psymbol * pmodule_type) list;
  pmsig_body   : pmodule_sig_struct_body;
}

and pmodule_sig_struct_body = pmodule_sig_item list

and pmodule_sig_item = [
  | `FunctionDecl of pfunction_decl
]

and pvariable_decl = {
  pvd_name : psymbol;
  pvd_type : pty;
}

and fun_params = 
 | Fparams_exp of (psymbol * pty) list
 | Fparams_imp of pty

and pfunction_decl = {
  pfd_name     : psymbol;
  pfd_tyargs   : fun_params;
  pfd_tyresult : pty;
  pfd_uses     : bool * pqsymbol list option;
}

(* -------------------------------------------------------------------- *)
and pmodule_params = (psymbol * pmodule_type) list

and pmodule_expr_r =
  | Pm_ident  of pmodule_params * pmsymbol
  | Pm_struct of pstructure

and pmodule_expr = pmodule_expr_r located

and pstructure = {
  ps_params    : pmodule_params;
  ps_body      : pstructure_item located list;
  ps_signature : ((pqsymbol * psymbol list) located) list;
}

and pstructure_item =
  | Pst_mod    of pmodule
  | Pst_var    of (psymbol list * pty)
  | Pst_fun    of (pfunction_decl * pfunction_body)
  | Pst_alias  of (psymbol * pgamepath)

and pfunction_body = {
  pfb_locals : pfunction_local list;
  pfb_body   : pstmt;
  pfb_return : pexpr option;
}

and pfunction_local = {
  pfl_names : ([`Single|`Tuple] * (psymbol list)) located;
  pfl_type  : pty   option;
  pfl_init  : pexpr option;
}



and pmodule = (psymbol * pmodule_expr)

and ptopmodule = {
  ptm_def   : pmodule;
  ptm_local : bool;
}

and pdeclmodule = {
  ptmd_name  : psymbol;
  ptmd_modty : pmodule_type_restr;
}

(* -------------------------------------------------------------------- *)
type ptyparams = (psymbol * pqsymbol list) list

type ptydecl = {
  pty_name   : psymbol;
  pty_tyvars : ptyparams;
  pty_body   : ptydbody;
}

and ptydbody =
| PTYD_Abstract
| PTYD_Alias    of pty
| PTYD_Record   of precord
| PTYD_Datatype of pdatatype

and pdatatype = (psymbol * pty list) list

and precord = (psymbol * pty) list

(* -------------------------------------------------------------------- *)
type pmemory   = psymbol

type phoarecmp = PFHle | PFHeq | PFHge

type glob_or_var = 
  | GVglob of pmsymbol located 
  | GVvar  of pqsymbol

type pformula  = pformula_r located

and pformula_r =
  | PFhole
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
  | PFrecord of pformula rfield list
  | PFproj   of pformula * pqsymbol
  | PFproji  of pformula * int 
  | PFglob   of pmsymbol located 
  | PFeqveq  of glob_or_var list
  | PFlsless of pgamepath
  | PFscope  of pqsymbol * pformula

  (* for claims *)
  | PFhoareS   of pformula * pfunction_body located * pformula
  | PFhoareF   of pformula * pgamepath * pformula
  | PFequivF   of pformula * (pgamepath * pgamepath) * pformula
  | PFeagerF    of pformula * (pstmt * pgamepath * pgamepath * pstmt) * pformula
  | PFprob     of pgamepath * (pformula list) * pmemory * pformula
  | PFBDhoareS of pformula * pfunction_body located * pformula * phoarecmp * pformula
  | PFBDhoareF of pformula * pgamepath * pformula * phoarecmp * pformula

and pgtybinding  = psymbol list * pgty
and pgtybindings = pgtybinding list

and pgty =
| PGTY_Type  of pty
| PGTY_ModTy of pmodule_type_restr
| PGTY_Mem

let rec pf_ident f =
  match unloc f with
  | PFident ({ pl_desc = ([], x) }, _) -> Some x
  | PFtuple [f] -> pf_ident f
  | _ -> None

(* -------------------------------------------------------------------- *)
type pop_def =
  | PO_abstr of pty
  | PO_concr of ptybindings * pty * pexpr
  | PO_case  of ptybindings * pty * pop_branch list

and pop_branch = {
  pop_patterns : pop_pattern list;
  pop_body     : pexpr;
}

and pop_pattern = {
  pop_name    : psymbol;
  pop_tvi     : ptyannot option;
  pop_pattern : pqsymbol * psymbol list;
}

type poperator = {
  po_kind   : [`Op | `Const];
  po_name   : psymbol;
  po_tyvars : (psymbol * pqsymbol list) list option;
  po_def    : pop_def
}

type ppred_def = 
  | PPabstr of pty list
  | PPconcr of ptybindings * pformula  

type ppredicate = {
  pp_name   : psymbol;
  pp_tyvars : (psymbol * pqsymbol list) list option;
  pp_def    : ppred_def;
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
  | EA_none 
  | EA_mod  of pmsymbol located

type 'a fpattern = { 
  fp_kind : 'a fpattern_kind;
  fp_args : fpattern_arg located list 
}

type ffpattern = pformula fpattern

type pformula_o = pformula option

type cfpattern = (pformula_o * pformula_o) fpattern
type ccfpattern =  
  ((pformula_o * pformula_o) * 
   (phoarecmp option * pformula) option) fpattern

type preduction = {
  pbeta    : bool;
  pdelta   : pqsymbol list option;
  pzeta    : bool;   (* remove let *)
  piota    : bool;   (* remove case *)
  plogic   : bool;   (* perform logical simplification *)
  pmodpath : bool;   (* normalize modpath *)
}

type pterm = {
  pt_name : pqsymbol;
  pt_tys  : ptyannot option;
  pt_args : fpattern_arg located list;
}

(* -------------------------------------------------------------------- *)
type 'a doption = 
  | Single of 'a
  | Double of 'a * 'a

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

type codepos = int * ((int * codepos) option)

type call_info = 
  | CI_spec of (pformula * pformula)
  | CI_inv  of pformula
  | CI_upto of (pformula * pformula * pformula_o)
  
(* AppSingle are optional for bounded Phl judgments
   AppMult is required by most general rule for upper bounded Phl
   AppNone is required for the rest of judgments 
*)

type p_app_bd_info = 
  | PAppNone 
  | PAppSingle of pformula 
  | PAppMult   of pformula_o tuple5

type ('a, 'b, 'c) rnd_tac_info = 
  | PNoRndParams 
  | PSingleRndParam of 'c 
  | PTwoRndParams   of 'a * 'a 
  | PMultRndParams  of ('a tuple5) * 'b

type tac_dir = Backs | Fwds

type pfel_spec_preds = (pgamepath*pformula) list
 
type trans_kind = 
  | TKfun of pgamepath 
  | TKstmt of tac_side * pstmt

type trans_info = 
  trans_kind * pformula * pformula * pformula * pformula

type eager_info = 
  | LE_done of psymbol 
  | LE_todo of psymbol * pstmt * pstmt * pformula * pformula

type bdh_split = 
  | BDH_split_bop of pformula * pformula * pformula option
  | BDH_split_or_case of pformula * pformula * pformula 
  | BDH_split_not of pformula option * pformula

type phltactic = 
  | Pfun_def  
  | Pfun_abs    of pformula
  | Pfun_upto   of (pformula * pformula * pformula_o)
  | Pfun_to_code 
  | Pskip
  | Papp        of (tac_dir * int doption * pformula * p_app_bd_info)
  | Pwp         of int doption option 
  | Pwhile      of tac_side * (pformula * pformula_o * (pformula * pformula) option)
  | Pfission    of (tac_side * codepos * (int * (int * int)))
  | Pfusion     of (tac_side * codepos * (int * (int * int)))
  | Punroll     of (tac_side * codepos)
  | Psplitwhile of (pexpr * tac_side * codepos )
  | Pcall       of tac_side * call_info fpattern 
  | Prcond      of (bool option * bool * int)
  | Pcond       of tac_side 
  | Pswap       of ((tac_side * swap_kind) located list)
  | Pcfold      of (tac_side * codepos * int option)
  | Pinline     of pinline_arg
  | Pkill       of (tac_side * codepos * int option)
  | Prnd        of tac_side * (pformula, pformula option, pformula) rnd_tac_info
  | Palias      of (tac_side * codepos * psymbol option)
  | Pset        of (bool * tac_side * codepos * psymbol * pexpr)
  | Pconseq     of bool*(ccfpattern option * ccfpattern option * ccfpattern option)
  | Phr_exists_elim  
  | Phr_exists_intro of pformula list 
  | Pexfalso
  | Pbydeno       of ([`PHoare | `Equiv ] * cfpattern)
  | PPr           of (pformula * pformula) option 
  | Pfel          of int * (pformula * pformula * pformula * pformula * pfel_spec_preds * pformula option)
  | Phoare
  | Pprbounded
  | Psim           of (pformula_o * pformula_o * pformula_o)
  | Ptrans_stmt    of trans_info
  | Psymmetry
  | Psp            of (bool option)
  | Pbdhoare_split of bdh_split 

    (* Eager *)
  | Peager_seq       of eager_info * (int * int) * pformula 
  | Peager_if  
  | Peager_while     of eager_info
  | Peager_fun_def 
  | Peager_fun_abs   of eager_info * pformula
  | Peager_call      of call_info fpattern
  | Peager           of eager_info * pformula

    (* Relation between logic *)
  | Pbd_equiv of (bool * pformula * pformula)

and pinline_arg =
  [ `ByName    of tac_side * (pgamepath list * int list option)
  | `ByPattern of pipattern
  | `All       of tac_side ]

type trepeat = [`All | `Maybe] * int option
type tfocus  = (int option * int option) * [`Include | `Exclude]

type rwarg = (tfocus located) option * rwarg1

and rwarg1 =
  | RWDelta of (rwside * rwocc * pformula)
  | RWRw    of (rwside * trepeat option * rwocc * ffpattern list)
  | RWPr    of psymbol
  | RWDone  of bool
  | RWSimpl

and rwside = [`LtoR | `RtoL]
and rwocc  = Sint.t option

type intropattern1 =
  | IPCore  of renaming located
  | IPCase  of intropattern list
  | IPRw    of (rwocc * rwside)
  | IPClear of psymbol list
  | IPDone  of bool
  | IPSimplify

and intropattern = intropattern1 list

and renaming = [
  `NoName | `FindName | `WithRename of string | `NoRename of string
]

type pdbmap1 = {
  pht_flag : [ `Include | `Exclude ];
  pht_kind : [ `Theory  | `Lemma   ];
  pht_name : pqsymbol;
}

and pdbhint = {
  pht_nolocals : bool;
  pht_map : pdbmap1 list;
}

type logtactic =
  | Preflexivity
  | Passumption of (pqsymbol option * ptyannot option)
  | Psmt        of (pdbhint option * pprover_infos)
  | Pintro      of intropattern
  | Psplit                        
  | Pfield		of psymbol list
  | Pring 		of psymbol list
  | Pexists     of fpattern_arg located list
  | Pleft                         
  | Pright                        
  | Ptrivial
  | Pcongr
  | Pelim       of ffpattern 
  | Papply      of (ffpattern * psymbol option)
  | Pcut        of (intropattern1 option * pformula * ptactic_core option)
  | Pcutdef     of (intropattern1 option * pterm)
  | Pgeneralize of (rwocc * pformula) list
  | Pclear      of psymbol list
  | Prewrite    of rwarg list
  | Psubst      of pformula list
  | Psimplify   of preduction 
  | Pchange     of pformula
  | PelimT      of (pformula * pqsymbol option)
  | Ppose       of (psymbol * rwocc * pformula)

and ptactic_core_r =
  | Pidtac      of string option
  | Pdo         of trepeat * ptactic_core
  | Ptry        of ptactic_core
  | Pby         of (ptactic list) option
  | Por         of ptactic * ptactic
  | Pseq        of ptactic list
  | Pcase       of pformula 
  | Plogic      of logtactic
  | PPhl        of phltactic
  | Pprogress   of ptactic_core option
  | Psubgoal    of ptactic_chain
  | Padmit
  | Pdebug

and ptactic_core = ptactic_core_r located

and ptactic = {
  pt_core   : ptactic_core;
  pt_intros : intropattern;
}

and ptactic_chain =
  | Psubtacs of ptactic list
  | Pfirst   of ptactic * int
  | Plast    of ptactic * int
  | Protate  of [`Left | `Right] * int

(* -------------------------------------------------------------------- *)
type paxiom_kind = PAxiom | PLemma of ptactic option | PILemma

type paxiom = {
  pa_name    : psymbol;
  pa_tyvars  : (psymbol * pqsymbol list) list option;
  pa_vars    : pgtybindings option;  
  pa_formula : pformula;
  pa_kind    : paxiom_kind;
  pa_nosmt   : bool;
  pa_local   : bool;
}

(* -------------------------------------------------------------------- *)
type ptypeclass = {
  ptc_name : psymbol;
  ptc_inth : pqsymbol option;
  ptc_ops  : (psymbol * pty) list;
  ptc_axs  : pformula list;
}

type ptycinstance = {
  pti_name : pqsymbol;
  pti_type : pqsymbol;
  pti_ops  : (psymbol * pqsymbol) list;
  pti_axs  : (psymbol * ptactic_core) list;
}

(* -------------------------------------------------------------------- *)
type ident_spec = psymbol list

type inv = (pformula, (pformula * pformula) * pformula_o) EcAstlogic.g_inv

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
  | Pr_ty  of pqsymbol
  | Pr_op  of pqsymbol
  | Pr_th  of pqsymbol
  | Pr_pr  of pqsymbol
  | Pr_ax  of pqsymbol
  | Pr_mod of pqsymbol
  | Pr_mty of pqsymbol

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
  pthc_ext  : (pqsymbol * theory_override) list;
  pthc_prf  : theory_cloning_proof list;
}

and theory_cloning_proof = {
  pthp_mode   : [ `All   of pqsymbol option
                | `Named of pqsymbol];
  pthp_tactic : ptactic_core option;
}

and theory_override =
| PTHO_Type   of ty_override
| PTHO_Op     of op_override
| PTHO_Pred   of pr_override
| PTHO_Theory of pqsymbol

and ty_override = psymbol list * pty * [`Alias | `Inline]
and op_override = op_override_def * [`Alias | `Inline]

and op_override_def = {
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
type toextract = 
 | ExOp of pqsymbol
 | ExTy of pqsymbol
 | ExTh of pqsymbol

type withextract = toextract * string 

(* -------------------------------------------------------------------- *)
type proofmode = {
  pm_strict : bool;
}

(* -------------------------------------------------------------------- *)
type global =
  | Gmodule      of ptopmodule
  | Gdeclare     of pdeclmodule
  | Ginterface   of (psymbol * pmodule_sig)
  | Goperator    of poperator
  | Gpredicate   of ppredicate
  | Gaxiom       of paxiom
  | Gclaim       of claim
  | Gtype        of ptydecl list
  | Gtypeclass   of ptypeclass
  | Gtycinstance of ptycinstance
  | Gprint       of pprint
  | GthOpen      of psymbol
  | GthClose     of psymbol
  | GthRequire   of (psymbol * [`Import|`Export] option)
  | GthImport    of pqsymbol
  | GthExport    of pqsymbol
  | GthClone     of (theory_cloning * [`Import|`Export] option)
  | GthW3        of (string list * string * w3_renaming list)
  | GsctOpen
  | GsctClose
  | Grealize     of pqsymbol
  | Gtactics     of [`Proof of proofmode | `Actual of ptactic list]
  | Gprover_info of pprover_infos
  | Gsave        of EcLocation.t
  | Gpragma      of psymbol
  | Gextract     of (string option * toextract list * withextract list)

type prog =
  | P_Prog of (global located) list * bool
  | P_Undo of int
