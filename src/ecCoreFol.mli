(* -------------------------------------------------------------------- *)
open EcBigInt
open EcPath
open EcAst
open EcMaps
open EcIdent
open EcTypes
open EcCoreModules
open EcMemory

(* -------------------------------------------------------------------- *)
type quantif = EcAst.quantif

type hoarecmp = EcAst.hoarecmp

type gty = EcAst.gty

type binding  = (EcIdent.t * gty)
type bindings = binding list

type form     = EcAst.form
type f_node   = EcAst.f_node
type eagerF   = EcAst.eagerF
type equivF   = EcAst.equivF
type equivS   = EcAst.equivS
type sHoareF  = EcAst.sHoareF
type sHoareS  = EcAst.sHoareS
type eHoareF  = EcAst.eHoareF
type eHoareS  = EcAst.eHoareS
type bdHoareF = EcAst.bdHoareF
type bdHoareS = EcAst.bdHoareS
type pr       = EcAst.pr

type module_type = EcAst.module_type

type mod_restr = EcAst.mod_restr

(* -------------------------------------------------------------------- *)
val gtty    : EcTypes.ty -> gty
val gtmodty : mty_mr -> gty
val gtmem   : EcMemory.memtype -> gty

(* -------------------------------------------------------------------- *)
val as_gtty  : gty -> EcTypes.ty
val as_modty : gty -> mty_mr
val as_mem   : gty -> EcMemory.memtype

(* -------------------------------------------------------------------- *)
val gty_equal : gty -> gty -> bool
val gty_fv    : gty -> int Mid.t

(* -------------------------------------------------------------------- *)
val mty_equal : module_type -> module_type -> bool
val mty_hash  : module_type -> int

val mr_equal : mod_restr -> mod_restr -> bool
val mr_hash  : mod_restr -> int

(* -------------------------------------------------------------------- *)
val f_equal   : form -> form -> bool
val f_compare : form -> form -> int
val f_hash    : form -> int
val f_fv      : form -> int Mid.t
val f_ty      : form -> EcTypes.ty
val f_ops     : form -> Sp.t

module Mf : Map.S with type key = form
module Sf : Set.S with module M = Map.MakeBase(Mf)
module Hf : EHashtbl.S with type key = form

(* -------------------------------------------------------------------- *)
val mk_form : f_node -> EcTypes.ty -> form
val f_node  : form -> f_node

(* -------------------------------------------------------------------- *)
(* not recursive *)
val f_map  : (EcTypes.ty -> EcTypes.ty) -> (form -> form) -> form -> form
val f_iter : (form -> unit) -> form -> unit
val form_exists: (form -> bool) -> form -> bool
val form_forall: (form -> bool) -> form -> bool

(* -------------------------------------------------------------------- *)
val gty_as_ty  : gty -> EcTypes.ty
val gty_as_mem : gty -> EcMemory.memtype
val gty_as_mod : gty -> mty_mr
val kind_of_gty: gty -> [`Form | `Mem | `Mod]

(* soft-constructors - common leaves *)
val f_local : EcIdent.t -> EcTypes.ty -> form
val f_pvar  : EcTypes.prog_var -> EcTypes.ty -> memory -> ss_inv
val f_pvarg : EcTypes.ty -> memory -> ss_inv
val f_pvloc : variable -> memory -> ss_inv
val f_glob  : EcIdent.t -> memory -> ss_inv

(* soft-constructors - common formulas constructors *)
val f_op     : path -> EcTypes.ty list -> EcTypes.ty -> form
val f_app    : form -> form list -> EcTypes.ty -> form
val f_tuple  : form list -> form
val f_proj   : form -> int -> EcTypes.ty -> form
val f_if     : form -> form -> form -> form
val f_match  : form -> form list -> EcTypes.ty -> form
val f_let    : EcTypes.lpattern -> form -> form -> form
val f_let1   : EcIdent.t -> form -> form -> form
val f_quant  : quantif -> bindings -> form -> form
val f_exists : bindings -> form -> form
val f_forall : bindings -> form -> form
val f_lambda : bindings -> form -> form

val f_forall_mems : (EcIdent.t * memtype) list -> form -> form

val f_hoareF : ss_inv -> xpath -> ss_inv -> form
val f_hoareS : memtype -> ss_inv -> stmt -> ss_inv -> form

val f_eHoareF : ss_inv -> xpath -> ss_inv -> form
val f_eHoareS : memtype -> ss_inv -> EcCoreModules.stmt -> ss_inv -> form

(* soft-constructors - eager *)

(* soft-constructors - bd hoare *)
val hoarecmp_opp : hoarecmp -> hoarecmp

val f_bdHoareF : ss_inv -> xpath -> ss_inv -> hoarecmp -> ss_inv -> form
val f_bdHoareS : memtype -> ss_inv -> stmt -> ss_inv -> hoarecmp -> ss_inv -> form

(* soft-constructors - equiv *)
val f_equivF : ts_inv -> xpath -> xpath -> ts_inv -> form
val f_equivS : memtype -> memtype -> ts_inv -> stmt -> stmt -> ts_inv -> form

(* soft-constructors - eager *)
val f_eagerF : ts_inv -> stmt -> xpath -> xpath -> stmt -> ts_inv -> form

(* soft-constructors - Pr *)
val f_pr_r : pr -> form
val f_pr   : memory -> xpath -> form -> ss_inv -> form

(* soft-constructors - unit *)
val f_tt : form

(* soft-constructors - bool *)
val f_bool  : bool -> form
val f_true  : form
val f_false : form

(* soft-constructors - boolean operators *)
val fop_not  : form
val fop_and  : form
val fop_anda : form
val fop_or   : form
val fop_ora  : form
val fop_imp  : form
val fop_iff  : form
val fop_eq   : EcTypes.ty -> form

val f_not   : form -> form
val f_and   : form -> form -> form
val f_ands  : form list -> form
val f_anda  : form -> form -> form
val f_andas : form list -> form
val f_or    : form -> form -> form
val f_ors   : form list -> form
val f_ora   : form -> form -> form
val f_oras  : form list -> form
val f_imp   : form -> form -> form
val f_imps  : form list -> form -> form
val f_iff   : form -> form -> form

val f_eq  : form -> form -> form
val f_eqs : form list -> form list -> form

(* soft-constructors - integers *)
val fop_int_opp : form
val fop_int_add : form
val fop_int_pow : form

val f_i0  : form
val f_i1  : form
val f_im1 : form

val f_int       : zint -> form
val f_int_add   : form -> form -> form
val f_int_sub   : form -> form -> form
val f_int_opp   : form -> form
val f_int_mul   : form -> form -> form
val f_int_pow   : form -> form -> form
val f_int_edivz : form -> form -> form

(* -------------------------------------------------------------------- *)
val f_none : ty -> form
val f_some : form -> form

(* -------------------------------------------------------------------- *)
val f_is_inf : form -> form
val f_is_int : form -> form

val f_Inf   : form
val f_N     : form -> form
val f_xopp  : form -> form
val f_xadd  : form -> form -> form
val f_xmul  : form -> form -> form
val f_xmuli : form -> form -> form

val f_x0 : form
val f_x1 : form

val f_xadd_simpl  : form -> form -> form
val f_xmul_simpl  : form -> form -> form
val f_xmuli_simpl : form -> form -> form

(* -------------------------------------------------------------------- *)
val string_of_quant : quantif -> string

(* -------------------------------------------------------------------- *)
exception DestrError of string

val destr_error : string -> 'a

(* -------------------------------------------------------------------- *)
val destr_app1 : name:string -> (path -> bool) -> form -> form
val destr_app2 : name:string -> (path -> bool) -> form -> form * form

val destr_app1_eq : name:string -> path -> form -> form
val destr_app2_eq : name:string -> path -> form -> form * form

val decompose_binder  : ?bound:int -> quantif:quantif -> form -> bindings * form
val decompose_forall  : ?bound:int -> form -> bindings * form
val decompose_exists  : ?bound:int -> form -> bindings * form
val decompose_lambda  : ?bound:int -> form -> bindings * form

val destr_binder  : ?bound:int -> quantif:quantif -> form -> bindings * form
val destr_forall  : ?bound:int -> form -> bindings * form
val destr_exists  : ?bound:int -> form -> bindings * form
val destr_lambda  : ?bound:int -> form -> bindings * form

val destr_binder1  : quantif:quantif -> form -> ident * gty * form
val destr_forall1  : form -> ident * gty * form
val destr_exists1  : form -> ident * gty * form
val destr_lambda1  : form -> ident * gty * form

val destr_op        : form -> EcPath.path * ty list
val destr_local     : form -> EcIdent.t
val destr_pvar      : form -> prog_var * memory
val destr_proj      : form -> form * int
val destr_tuple     : form -> form list
val destr_app       : form -> form * form list
val destr_op_app    : form -> (EcPath.path * ty list) * form list
val destr_not       : form -> form
val destr_nots      : form -> bool * form
val destr_and       : form -> form * form
val destr_and3      : form -> form * form * form
val destr_and_r     : form -> [`Sym | `Asym] * (form * form)
val destr_or        : form -> form * form
val destr_or_r      : form -> [`Sym | `Asym] * (form * form)
val destr_imp       : form -> form * form
val destr_iff       : form -> form * form
val destr_eq        : form -> form * form
val destr_eq_or_iff : form -> form * form
val destr_let       : form -> lpattern * form * form
val destr_let1      : form -> EcIdent.t * ty * form * form
val destr_equivF    : form -> equivF
val destr_equivS    : form -> equivS
val destr_eagerF    : form -> eagerF
val destr_hoareF    : form -> sHoareF
val destr_hoareS    : form -> sHoareS
val destr_eHoareF   : form -> eHoareF
val destr_eHoareS   : form -> eHoareS
val destr_bdHoareF  : form -> bdHoareF
val destr_bdHoareS  : form -> bdHoareS
val destr_pr        : form -> pr
val destr_programS  : [`Left | `Right] option -> form -> memenv * stmt
val destr_int       : form -> zint

val destr_glob      : form -> EcIdent.t        * memory
val destr_pvar      : form -> EcTypes.prog_var * memory

(* -------------------------------------------------------------------- *)
val is_true      : form -> bool
val is_false     : form -> bool
val is_tuple     : form -> bool
val is_not       : form -> bool
val is_and       : form -> bool
val is_or        : form -> bool
val is_imp       : form -> bool
val is_iff       : form -> bool
val is_forall    : form -> bool
val is_exists    : form -> bool
val is_lambda    : form -> bool
val is_let       : form -> bool
val is_eq        : form -> bool
val is_op        : form -> bool
val is_local     : form -> bool
val is_pvar      : form -> bool
val is_proj      : form -> bool
val is_equivF    : form -> bool
val is_equivS    : form -> bool
val is_eagerF    : form -> bool
val is_hoareF    : form -> bool
val is_hoareS    : form -> bool
val is_eHoareF   : form -> bool
val is_eHoareS   : form -> bool
val is_bdHoareF  : form -> bool
val is_bdHoareS  : form -> bool
val is_pr        : form -> bool
val is_eq_or_iff : form -> bool

(* -------------------------------------------------------------------- *)
val split_fun  : form -> bindings * form
val split_args : form -> form * form list

(* -------------------------------------------------------------------- *)
val form_of_expr : EcTypes.expr -> form
val ss_inv_of_expr : EcMemory.memory -> EcTypes.expr -> ss_inv

(* -------------------------------------------------------------------- *)
exception CannotTranslate

val expr_of_ss_inv : ss_inv -> EcTypes.expr
val expr_of_form : form -> EcTypes.expr

(* -------------------------------------------------------------------- *)
(* A predicate on memory: λ mem. -> pred *)

(* -------------------------------------------------------------------- *)
(* A predicate on memory: λ mem. -> pred *)
type mem_pr = EcMemory.memory * form

(* -------------------------------------------------------------------- *)
val can_subst : form -> bool

(* -------------------------------------------------------------------- *)
type core_op = [
  | `True
  | `False
  | `Not
  | `And of [`Asym | `Sym]
  | `Or  of [`Asym | `Sym]
  | `Imp
  | `Iff
  | `Eq
]

val core_op_kind : path -> core_op option
