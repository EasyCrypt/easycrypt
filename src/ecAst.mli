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

(* We use the alert system for privacy because we want to 
   permit access in *some* instances, and the other fields are fine *)
(* This is to ensure that memory bindings are carried along with the invariants *)
and eagerF = {
  eg_ml : memory;
  eg_mr : memory;
  eg_pr : form;
  [@alert priv_pl "Use the accessor function `eg_pr` instead of the field"]
  eg_sl : stmt;  (* No local program variables *)
  eg_fl : EcPath.xpath;
  eg_fr : EcPath.xpath;
  eg_sr : stmt;  (* No local program variables *)
  eg_po : form
  [@alert priv_pl "Use the accessor function `es_po` instead of the field"]
}

and equivF = {
  ef_ml : memory;
  ef_mr : memory;
  ef_pr : form;
  [@alert priv_pl "Use the accessor function `ef_pr` instead of the field"]
  ef_fl : EcPath.xpath;
  ef_fr : EcPath.xpath;
  ef_po : form;
  [@alert priv_pl "Use the accessor function `ef_po` instead of the field"]
}

and equivS = {
  es_ml  : memenv;
  es_mr  : memenv;
  es_pr  : form;
  [@alert priv_pl "Use the accessor function `es_pr` instead of the field"]
  es_sl  : stmt;
  es_sr  : stmt;
  es_po  : form;
  [@alert priv_pl "Use the accessor function `es_po` instead of the field"]
}

and sHoareF = {
  hf_m : memory;
  hf_pr : form;
  [@alert priv_pl "Use the accessor function `hf_pr` instead of the field"]
  hf_f  : EcPath.xpath;
  hf_po : form;
  [@alert priv_pl "Use the accessor function `hf_pr` instead of the field"]
}

and sHoareS = {
  hs_m  : memenv;
  hs_pr : form;
  [@alert priv_pl "Use the accessor function `hs_pr` instead of the field"]
  hs_s  : stmt;
  hs_po : form;
  [@alert priv_pl "Use the accessor function `hs_po` instead of the field"]
}


and eHoareF = {
  ehf_m  : memory;
  ehf_pr  : form;
  [@alert priv_pl "Use the accessor function `ehf_pr` instead of the field"]
  ehf_f   : EcPath.xpath;
  ehf_po  : form;
  [@alert priv_pl "Use the accessor function `ehf_po` instead of the field"]
}

and eHoareS = {
  ehs_m   : memenv;
  ehs_pr  : form;
  [@alert priv_pl "Use the accessor function `ehs_pr` instead of the field"]
  ehs_s   : stmt;
  ehs_po  : form;
  [@alert priv_pl "Use the accessor function `ehs_po` instead of the field"]
}

and bdHoareF = {
  bhf_m   : memory;
  bhf_pr  : form;
  [@alert priv_pl "Use the accessor function `bhf_pr` instead of the field"]
  bhf_f   : EcPath.xpath;
  bhf_po  : form;
  [@alert priv_pl "Use the accessor function `bhf_po` instead of the field"]
  bhf_cmp : hoarecmp;
  bhf_bd  : form;
  [@alert priv_pl "Use the accessor function `bhf_bd` instead of the field"]
}

and bdHoareS = {
  bhs_m   : memenv;
  bhs_pr  : form;
  [@alert priv_pl "Use the accessor function `bhs_pr` instead of the field"]
  bhs_s   : stmt;
  bhs_po  : form;
  [@alert priv_pl "Use the accessor function `bhs_po` instead of the field"]
  bhs_cmp : hoarecmp;
  bhs_bd  : form;
  [@alert priv_pl "Use the accessor function `bhs_bd` instead of the field"]
}

and ss_inv = {
  m   : memory;
  inv : form;
}

and pr = {
  pr_mem   : memory;
  pr_fun   : EcPath.xpath;
  pr_args  : form;
  pr_event : ss_inv;
}

(* -------------------------------------------------------------------- *)

val map_ss_inv : ?m:memory -> (form list -> form) -> ss_inv list -> ss_inv
val map_ss_inv1 : (form -> form) -> ss_inv -> ss_inv
val map_ss_inv2 : (form -> form -> form) -> ss_inv -> ss_inv -> ss_inv
val map_ss_inv3 : (form -> form -> form -> form) -> ss_inv -> ss_inv -> ss_inv -> ss_inv

val map_ss_inv_destr2 : (form -> form * form) -> ss_inv -> ss_inv * ss_inv
val map_ss_inv_destr3 : (form -> form * form * form) -> ss_inv -> ss_inv * ss_inv * ss_inv

type ts_inv = {
  ml  : memory;
  mr  : memory;
  inv : form;
}

val map_ts_inv : ?ml:memory -> ?mr:memory -> (form list -> form) -> ts_inv list -> ts_inv
val map_ts_inv1 : (form -> form) -> ts_inv -> ts_inv
val map_ts_inv2 : (form -> form -> form) -> ts_inv -> ts_inv -> ts_inv
val map_ts_inv3 : (form -> form -> form -> form) -> ts_inv -> ts_inv -> ts_inv -> ts_inv

val map_ts_inv_left : (ss_inv list -> ss_inv) -> ts_inv list -> ts_inv
val map_ts_inv_left1 : (ss_inv -> ss_inv) -> ts_inv -> ts_inv
val map_ts_inv_left2 : (ss_inv -> ss_inv -> ss_inv) -> ts_inv -> ts_inv -> ts_inv
val map_ts_inv_left3 : (ss_inv -> ss_inv -> ss_inv -> ss_inv) -> 
    ts_inv -> ts_inv -> ts_inv -> ts_inv

val map_ts_inv_right : (ss_inv list -> ss_inv) -> ts_inv list -> ts_inv
val map_ts_inv_right1 : (ss_inv -> ss_inv) -> ts_inv -> ts_inv
val map_ts_inv_right2 : (ss_inv -> ss_inv -> ss_inv) -> ts_inv -> ts_inv -> ts_inv
val map_ts_inv_right3 : (ss_inv -> ss_inv -> ss_inv -> ss_inv) -> 
    ts_inv -> ts_inv -> ts_inv -> ts_inv

val map_ts_inv_destr2 : (form -> form * form) -> ts_inv -> ts_inv * ts_inv
val map_ts_inv_destr3 : (form -> form * form * form) -> ts_inv -> ts_inv * ts_inv * ts_inv

val ts_inv_lower_left : (ss_inv list -> form) -> ts_inv list -> ss_inv
val ts_inv_lower_left1 : (ss_inv -> form) -> ts_inv -> ss_inv
val ts_inv_lower_left2 : (ss_inv -> ss_inv -> form) -> ts_inv -> ts_inv -> ss_inv
val ts_inv_lower_left3 : (ss_inv -> ss_inv -> ss_inv -> form) -> 
    ts_inv -> ts_inv -> ts_inv -> ss_inv

val ts_inv_lower_right : (ss_inv list -> form) -> ts_inv list -> ss_inv
val ts_inv_lower_right1 : (ss_inv -> form) -> ts_inv -> ss_inv
val ts_inv_lower_right2 : (ss_inv -> ss_inv -> form) -> ts_inv -> ts_inv -> ss_inv
val ts_inv_lower_right3 : (ss_inv -> ss_inv -> ss_inv -> form) -> 
    ts_inv -> ts_inv -> ts_inv -> ss_inv

(* -------------------------------------------------------------------- *)

type inv =
  | Inv_ss of ss_inv
  | Inv_ts of ts_inv

val inv_of_inv : inv -> form

val lift_ss_inv : (ss_inv -> 'a) -> inv -> 'a
val lift_ss_inv2 : (ss_inv -> ss_inv -> 'a) -> inv -> inv -> 'a
val lift_ss_inv3 : (ss_inv -> ss_inv -> ss_inv -> 'a) -> inv -> inv -> inv -> 'a
val lift_ts_inv : (ts_inv -> 'a) -> inv -> 'a
val lift_ts_inv2 : (ts_inv -> ts_inv -> 'a) -> inv -> inv -> 'a

val ss_inv_generalize_left : ss_inv -> memory -> ts_inv
val ss_inv_generalize_right : ss_inv -> memory -> ts_inv

val map_inv : (form list -> form) -> inv list -> inv
val map_inv1 : (form -> form) -> inv -> inv
val map_inv2 : (form -> form -> form) -> inv -> inv -> inv
val map_inv3 : (form -> form -> form -> form) -> inv -> inv -> inv -> inv

val eg_pr : eagerF -> ts_inv
val eg_po : eagerF -> ts_inv
val ef_pr : equivF -> ts_inv
val ef_po : equivF -> ts_inv
val es_pr : equivS -> ts_inv
val es_po : equivS -> ts_inv
val hf_pr : sHoareF -> ss_inv
val hf_po : sHoareF -> ss_inv
val hs_pr : sHoareS -> ss_inv
val hs_po : sHoareS -> ss_inv
val ehf_pr : eHoareF -> ss_inv
val ehf_po : eHoareF -> ss_inv
val ehs_pr : eHoareS -> ss_inv
val ehs_po : eHoareS -> ss_inv
val bhf_pr : bdHoareF -> ss_inv
val bhf_po : bdHoareF -> ss_inv
val bhf_bd : bdHoareF -> ss_inv
val bhs_pr : bdHoareS -> ss_inv
val bhs_po : bdHoareS -> ss_inv
val bhs_bd : bdHoareS -> ss_inv

(* -------------------------------------------------------------------- *)

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
(* Hashconsing                                                       *)
(* ----------------------------------------------------------------- *)

val mk_ty : ty_node -> ty
val mk_expr : expr_node -> ty -> expr
val mk_form : f_node -> ty -> form
val mk_instr : instr_node -> instr
val stmt : instr list -> stmt
