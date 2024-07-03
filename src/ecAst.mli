(* -------------------------------------------------------------------- *)
open EcSymbols
open EcIdent
open EcPath

module BI = EcBigInt

type memory = EcIdent.t

(* -------------------------------------------------------------------- *)
type pvar_kind =
  | PVKglob
  | PVKloc

type prog_var =
  | PVglob of EcPath.xpath
  | PVloc of EcSymbols.symbol

type equantif  = [ `ELambda | `EForall | `EExists ]

type quantif =
  | Lforall
  | Lexists
  | Llambda

(* -------------------------------------------------------------------- *)
type hoarecmp = FHle | FHeq | FHge

(* -------------------------------------------------------------------- *)

type 'a use_restr = {
  ur_pos : 'a option;   (* If not None, can use only element in this set. *)
  ur_neg : 'a;          (* Cannot use element in this set. *)
}

type mr_xpaths = EcPath.Sx.t use_restr

type mr_mpaths = EcPath.Sm.t use_restr

(* -------------------------------------------------------------------- *)
type ty = private {
  ty_node : ty_node;
  ty_fv   : int Mid.t; (* only ident appearing in path *)
  ty_tag  : int;
}

and ty_node =
  | Tglob   of EcIdent.t (* The tuple of global variable of the module *)
  | Tunivar of EcUid.uid
  | Tvar    of EcIdent.t
  | Ttuple  of ty list
  | Tconstr of EcPath.path * ty list
  | Tfun    of ty * ty

(* -------------------------------------------------------------------- *)
and ovariable = {
  ov_name : EcSymbols.symbol option;
  ov_type : ty;
}

and variable = {
  v_name : EcSymbols.symbol;   (* can be "_" *)
  v_type : ty;
}

and lpattern =
  | LSymbol of (EcIdent.t * ty)
  | LTuple  of (EcIdent.t * ty) list
  | LRecord of EcPath.path * (EcIdent.t option * ty) list

and expr = private {
  e_node : expr_node;
  e_ty   : ty;
  e_fv   : int Mid.t;
  e_tag  : int;
}

and expr_node =
  | Eint   of BI.zint                      (* int. literal          *)
  | Elocal of EcIdent.t                    (* let-variables         *)
  | Evar   of prog_var                     (* module variable       *)
  | Eop    of EcPath.path * ty list        (* op apply to type args *)
  | Eapp   of expr * expr list             (* op. application       *)
  | Equant of equantif * ebindings * expr  (* fun/forall/exists     *)
  | Elet   of lpattern * expr * expr       (* let binding           *)
  | Etuple of expr list                    (* tuple constructor     *)
  | Eif    of expr * expr * expr           (* _ ? _ : _             *)
  | Ematch of expr * expr list * ty        (* match _ with _        *)
  | Eproj  of expr * int                   (* projection of a tuple *)

and ebinding  = EcIdent.t * ty
and ebindings = ebinding list

(* -------------------------------------------------------------------- *)

and lvalue =
  | LvVar   of (prog_var * ty)
  | LvTuple of (prog_var * ty) list

(* -------------------------------------------------------------------- *)
and instr = private {
  i_node : instr_node;
  i_fv : int Mid.t;
  i_tag  : int;
}

and instr_node =
  | Sasgn     of lvalue * expr
  | Srnd      of lvalue * expr
  | Scall     of lvalue option * EcPath.xpath * expr list
  | Sif       of expr * stmt * stmt
  | Swhile    of expr * stmt
  | Smatch    of expr * ((EcIdent.t * ty) list * stmt) list
  | Sassert   of expr
  | Sabstract of EcIdent.t

and stmt = private {
  s_node : instr list;
  s_fv   : int Mid.t;
  s_tag  : int;
}

and oracle_info = {
  oi_calls : xpath list;
}

and oracle_infos = oracle_info Msym.t

and mod_restr = (EcPath.Sx.t * EcPath.Sm.t) use_restr

and module_type = {
  mt_params : (EcIdent.t * module_type) list;
  mt_name   : EcPath.path;
  mt_args   : EcPath.mpath list;
}

(* -------------------------------------------------------------------- *)
and proj_arg =
  { arg_ty  : ty; (* type of the procedure argument "arg" *)
    arg_pos : int;       (* projection *)
  }

and local_memtype = {
  lmt_name : symbol option;      (* provides access to the full local memory *)
  lmt_decl : ovariable list;
  lmt_proj : (int * ty) Msym.t;  (* where to find the symbol in mt_decl and its type *)
  lmt_ty   : ty;                 (* ttuple (List.map v_type mt_decl) *)
  lmt_n    : int;                (* List.length mt_decl *)
}

and memtype =
  | Lmt_concrete of local_memtype option

and memenv = memory * memtype

(* -------------------------------------------------------------------- *)
and gty =
  | GTty    of ty
  | GTmodty of mty_mr
  | GTmem   of memtype

and mty_mr = module_type * mod_restr

and binding  = (EcIdent.t * gty)
and bindings = binding list

and form = private {
  f_node : f_node;
  f_ty   : ty;
  f_fv   : int Mid.t; (* local, memory, module ident *)
  f_tag  : int;
}

and f_node =
  | Fquant  of quantif * bindings * form
  | Fif     of form * form * form
  | Fmatch  of form * form list * ty
  | Flet    of lpattern * form * form
  | Fint    of BI.zint
  | Flocal  of EcIdent.t
  | Fpvar   of prog_var * memory
  | Fglob   of EcIdent.t * memory
  | Fop     of EcPath.path * ty list
  | Fapp    of form * form list
  | Ftuple  of form list
  | Fproj   of form * int

  | FhoareF of sHoareF (* $hr / $hr *)
  | FhoareS of sHoareS

  | FbdHoareF of bdHoareF (* $hr / $hr *)
  | FbdHoareS of bdHoareS

  | FeHoareF of eHoareF (* $hr / $hr *)
  | FeHoareS of eHoareS

  | FequivF of equivF (* $left,$right / $left,$right *)
  | FequivS of equivS

  | FeagerF of eagerF

  | Fpr of pr (* hr *)

and eagerF = {
  eg_pr : form;
  eg_sl : stmt;  (* No local program variables *)
  eg_fl : EcPath.xpath;
  eg_fr : EcPath.xpath;
  eg_sr : stmt;  (* No local program variables *)
  eg_po : form
}

and equivF = {
  ef_pr : form;
  ef_fl : EcPath.xpath;
  ef_fr : EcPath.xpath;
  ef_po : form;
}

and equivS = {
  es_ml  : memenv;
  es_mr  : memenv;
  es_pr  : form;
  es_sl  : stmt;
  es_sr  : stmt;
  es_po  : form; }

and sHoareF = {
  hf_pr : form;
  hf_f  : EcPath.xpath;
  hf_po : form;
}

and sHoareS = {
  hs_m  : memenv;
  hs_pr : form;
  hs_s  : stmt;
  hs_po : form; }


and eHoareF = {
  ehf_pr  : form;
  ehf_f   : EcPath.xpath;
  ehf_po  : form;
}

and eHoareS = {
  ehs_m   : memenv;
  ehs_pr  : form;
  ehs_s   : stmt;
  ehs_po  : form;
}

and bdHoareF = {
  bhf_pr  : form;
  bhf_f   : EcPath.xpath;
  bhf_po  : form;
  bhf_cmp : hoarecmp;
  bhf_bd  : form;
}

and bdHoareS = {
  bhs_m   : memenv;
  bhs_pr  : form;
  bhs_s   : stmt;
  bhs_po  : form;
  bhs_cmp : hoarecmp;
  bhs_bd  : form;
}

and pr = {
  pr_mem   : memory;
  pr_fun   : EcPath.xpath;
  pr_args  : form;
  pr_event : form;
}

type 'a equality = 'a -> 'a -> bool
type 'a hash = 'a -> int
type 'a fv   = 'a -> int EcIdent.Mid.t

val ty_equal : ty equality
val ty_hash  : ty hash
val ty_fv    : ty fv

(* -------------------------------------------------------------------- *)
val v_equal : variable equality
val v_hash  : variable hash

(* -------------------------------------------------------------------- *)
val pv_equal : prog_var equality
val pv_hash  : prog_var hash
val pv_fv    : prog_var fv

val pv_kind : prog_var -> pvar_kind
(* -------------------------------------------------------------------- *)
val idty_equal : (EcIdent.t * ty) equality
val idty_hash  : (EcIdent.t * ty) hash

val lp_equal : lpattern equality
val lp_hash  : lpattern hash
val lp_fv    : lpattern -> EcIdent.Sid.t

(* -------------------------------------------------------------------- *)
val e_equal : expr equality
val e_hash  : expr hash
val e_fv    : expr fv

(* -------------------------------------------------------------------- *)
val eqt_equal : equantif equality
val eqt_hash  : equantif hash

(* -------------------------------------------------------------------- *)
val lv_equal : lvalue equality
val lv_fv    : lvalue fv
val lv_hash  : lvalue hash

(* -------------------------------------------------------------------- *)
val i_equal : instr equality
val i_hash  : instr hash
val i_fv    : instr fv

val s_equal : stmt equality
val s_hash  : stmt hash
val s_fv    : stmt fv

(*-------------------------------------------------------------------- *)
val qt_equal : quantif equality
val qt_hash  : quantif hash

(*-------------------------------------------------------------------- *)
val f_equal : form equality
val f_hash  : form hash
val f_fv    : form fv

(* -------------------------------------------------------------------- *)
val oi_equal : oracle_info equality
val oi_hash  : oracle_info hash

(* -------------------------------------------------------------------- *)
val hcmp_hash : hoarecmp hash

(* -------------------------------------------------------------------- *)
val ov_equal : ovariable equality
val ov_hash  : ovariable hash

val v_equal : variable equality
val v_hash : variable hash

(* -------------------------------------------------------------------- *)
val ur_equal : 'a equality -> 'a use_restr equality
val ur_hash  : ('a -> 'b list) -> 'b hash -> 'a use_restr hash

val mr_xpaths : mod_restr -> mr_xpaths
val mr_mpaths : mod_restr -> mr_mpaths

val mr_xpaths_fv : mr_xpaths fv
val mr_mpaths_fv : mr_mpaths fv

val mr_equal : mod_restr equality
val mr_hash  : mod_restr hash
val mr_fv    : mod_restr fv

val mty_equal : module_type equality
val mty_hash  : module_type hash
val mty_fv    : module_type fv

val mty_mr_equal : mty_mr equality
val mty_mr_hash  : mty_mr hash
val mty_mr_fv    : mty_mr fv

(* -------------------------------------------------------------------- *)
val lmt_equal : ty equality -> local_memtype equality
val lmt_hash : local_memtype hash

val mt_equal_gen : ty equality -> memtype equality
val mt_equal : memtype equality
val mt_fv : memtype fv

val mem_equal : memory equality

val me_equal_gen : ty equality -> memenv equality
val me_equal : memenv equality
val me_hash : memenv hash

(*-------------------------------------------------------------------- *)
val gty_equal : gty equality
val gty_hash  : gty hash
val gty_fv    : gty fv

(*-------------------------------------------------------------------- *)

val b_equal : bindings equality
val b_hash : bindings hash

(* -------------------------------------------------------------------- *)
val i_equal   : instr equality
val i_hash    : instr hash
val i_fv      : instr fv

val s_equal   : stmt equality
val s_hash    : stmt hash
val s_fv      : stmt fv

(*-------------------------------------------------------------------- *)
val hf_equal  : sHoareF equality
val hf_hash   : sHoareF hash

val hs_equal  : sHoareS equality
val hs_hash   : sHoareS hash

val ehf_equal : eHoareF equality
val ehf_hash  : eHoareF hash

val ehs_equal : eHoareS equality
val ehs_hash  : eHoareS hash

val bhf_equal : bdHoareF equality
val bhf_hash  : bdHoareF hash

val bhs_equal : bdHoareS equality
val bhs_hash  : bdHoareS hash

val eqf_equal : equivF equality
val ef_hash   : equivF hash

val eqs_equal : equivS equality
val es_hash   : equivS hash

val egf_equal : eagerF equality
val eg_hash   : eagerF hash

val pr_equal  : pr equality
val pr_hash   : pr hash

(* ----------------------------------------------------------------- *)
(* Predefined memories                                               *)
(* ----------------------------------------------------------------- *)

val mhr    : memory
val mleft  : memory
val mright : memory

(* ----------------------------------------------------------------- *)
(* Hashconsing                                                       *)
(* ----------------------------------------------------------------- *)

val mk_ty : ty_node -> ty
val mk_expr : expr_node -> ty -> expr
val mk_form : f_node -> ty -> form
val mk_instr : instr_node -> instr
val stmt : instr list -> stmt
