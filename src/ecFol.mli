(* -------------------------------------------------------------------- *)
open EcDebug
open EcUtils
open EcMaps
open EcIdent
open EcTypes
open EcModules
open EcMemory

(* -------------------------------------------------------------------- *)
val mhr    : memory
val mleft  : memory
val mright : memory

type gty =
  | GTty    of EcTypes.ty
  | GTmodty of module_type * EcPath.Sm.t
  | GTmem   of EcMemory.memtype

val destr_gty : gty -> EcTypes.ty
val gty_equal : gty  -> gty -> bool
val gty_fv    : gty -> int Mid.t

type quantif = 
  | Lforall
  | Lexists
  | Llambda

type binding = (EcIdent.t * gty) list

type hoarecmp = FHle | FHeq | FHge

type form = private { 
  f_node : f_node;
  f_ty   : ty; 
  f_fv   : int Mid.t;
  f_tag  : int;
}

and f_node =
  | Fquant  of quantif * binding * form
  | Fif     of form * form * form
  | Flet    of lpattern * form * form
  | Fint    of int
  | Flocal  of EcIdent.t
  | Fpvar   of EcTypes.prog_var * memory
  | Fglob   of EcPath.mpath * memory 
  | Fop     of EcPath.path * ty list
  | Fapp    of form * form list
  | Ftuple  of form list

  | FhoareF of hoareF (* $hr / $hr *)
  | FhoareS of hoareS (* $hr  / $hr   *)

  | FbdHoareF of bdHoareF (* $hr / $hr *)
  | FbdHoareS of bdHoareS (* $hr  / $hr   *)

  | FequivF of equivF (* $left,$right / $left,$right *)
  | FequivS of equivS (* $left,$right / $left,$right *)

  | Fpr     of pr (* hr *)

and equivF = { 
  ef_pr : form;
  ef_fl : EcPath.xpath;
  ef_fr : EcPath.xpath;
  ef_po : form;
}

and equivS = {
  es_ml : EcMemory.memenv;
  es_mr : EcMemory.memenv;
  es_pr : form;
  es_sl : stmt;
  es_sr : stmt;
  es_po : form;
}

and hoareF = { 
  hf_pr  : form;
  hf_f   : EcPath.xpath;
  hf_po  : form;
}

and hoareS = {
  hs_m   : EcMemory.memenv;
  hs_pr  : form; 
  hs_s   : stmt;
  hs_po  : form;
}

and bdHoareF = {
  bhf_pr  : form; 
  bhf_f   : EcPath.xpath;
  bhf_po  : form;
  bhf_cmp : hoarecmp;
  bhf_bd  : form;
}

and bdHoareS = {
  bhs_m   : EcMemory.memenv;
  bhs_pr  : form; 
  bhs_s   : stmt;
  bhs_po  : form;
  bhs_cmp : hoarecmp;
  bhs_bd  : form;
}

and pr = memory * EcPath.xpath * form list * form

type app_bd_info =
| AppNone
| AppSingle of form
| AppMult   of (form * form * form * form)

(* -------------------------------------------------------------------- *)
val f_equal   : form -> form -> bool
val f_compare : form -> form -> int
val f_hash    : form -> int 
val f_fv      : form -> int Mid.t 
val f_ty      : form -> EcTypes.ty

module Mf : Map.S with type key = form
module Sf : Set.S with module M = Map.MakeBase(Mf)
module Hf : EHashtbl.S with type key = form

(* -------------------------------------------------------------------- *)
val f_dump : form -> dnode

(* -------------------------------------------------------------------- *)
val mk_form : f_node -> EcTypes.ty -> form

(* soft-constructors - common leaves *)
val f_local : EcIdent.t -> EcTypes.ty -> form
val f_pvar  : EcTypes.prog_var -> EcTypes.ty -> memory -> form
val f_pvloc : EcPath.xpath -> EcModules.variable -> memory -> form
val f_glob  : EcPath.mpath -> memory -> form

(* soft-constructors - common formulas constructors *)
val f_op     : EcPath.path -> EcTypes.ty list -> EcTypes.ty -> form
val f_app    : form -> form list -> EcTypes.ty -> form
val f_tuple  : form list -> form
val f_if     : form -> form -> form -> form
val f_let    : EcTypes.lpattern -> form -> form -> form
val f_let1   : EcIdent.t -> form -> form -> form
val f_quant  : quantif -> binding -> form -> form
val f_exists : binding -> form -> form
val f_forall : binding -> form -> form
val f_lambda : binding -> form -> form

(* soft-constructors - unit *)
val f_tt : form

(* soft-constructors - bool *)
val f_bool  : bool -> form
val f_true  : form
val f_false : form

(* soft-constructors - numbers *)
val f_int  : int -> form
val f_rint : int -> form

val f_real_of_int : form -> form

val f_r0 : form
val f_r1 : form

(* soft-constructors - hoare *)
val f_hoareF   : form -> EcPath.xpath -> form -> form 
val f_hoareS   : memenv -> form -> EcModules.stmt -> form -> form 
val f_hoareS_r : hoareS -> form

(* soft-constructors - bd hoare *)
val f_bdHoareF   : form -> EcPath.xpath -> form -> hoarecmp -> form -> form 
val f_bdHoareS   : memenv -> form -> EcModules.stmt -> form -> hoarecmp -> form -> form 
val f_bdHoareS_r : bdHoareS -> form
val f_losslessF  : EcPath.xpath -> form

(* soft-constructors - equiv *)
val f_equivF   : form -> EcPath.xpath -> EcPath.xpath -> form -> form 
val f_equivS   : memenv -> memenv -> form -> EcModules.stmt -> EcModules.stmt -> form -> form
val f_equivS_r : equivS -> form

(* soft-constructors - PR *)
val f_pr : memory -> EcPath.xpath -> form list -> form -> form

(* soft-constructors - boolean operators *)
val fop_not  : form
val fop_and  : form
val fop_anda : form
val fop_or   : form
val fop_ora  : form
val fop_imp  : form
val fop_iff  : form
val fop_eq   : EcTypes.ty -> form

val f_not  : form -> form
val f_and  : form -> form -> form
val f_ands : form list -> form
val f_anda : form -> form -> form
val f_or   : form -> form -> form
val f_ors  : form list -> form
val f_ora  : form -> form -> form
val f_imp  : form -> form -> form
val f_imps : form list -> form -> form
val f_iff  : form -> form -> form

val f_eq  : form -> form -> form
val f_eqs : form list -> form list -> form

val f_eqparams : EcPath.xpath -> variable list -> memory ->
                 EcPath.xpath -> variable list -> memory -> form
val f_eqres    : EcPath.xpath -> EcTypes.ty -> memory ->
                 EcPath.xpath -> EcTypes.ty -> memory -> form
val f_eqglob   : EcPath.mpath -> memory -> 
                 EcPath.mpath -> memory -> form 

(* soft-constructors - ordering *)
val f_int_le : form -> form -> form
val f_int_lt : form -> form -> form

val f_int_prod : form -> form -> form
val f_int_sum  : form -> form -> form
val f_int_sub  : form -> form -> form
val f_int_pow  : form -> form -> form

val f_real_le : form -> form -> form
val f_real_lt : form -> form -> form

val f_real_div  : form -> form -> form
val f_real_sum  : form -> form -> form
val f_real_sub  : form -> form -> form
val f_real_prod : form -> form -> form

(* soft constructors - distributions *)
val fop_in_supp : EcTypes.ty -> form
val fop_mu_x    : EcTypes.ty -> form

val f_in_supp : form -> form -> form
val f_mu      : form -> form -> form
val f_mu_x    : form -> form -> form
val f_weight  : EcTypes.ty -> form -> form

(* -------------------------------------------------------------------- *)
module FSmart : sig
  type a_local = EcIdent.t * ty
  type a_pvar  = prog_var * ty * memory
  type a_quant = quantif * binding * form
  type a_if    = form tuple3
  type a_let   = lpattern * form * form
  type a_op    = EcPath.path * ty list * ty
  type a_tuple = form list
  type a_app   = form * form list * ty

  val f_local : (form * a_local) -> a_local -> form
  val f_pvar  : (form * a_pvar ) -> a_pvar  -> form
  val f_quant : (form * a_quant) -> a_quant -> form
  val f_if    : (form * a_if   ) -> a_if    -> form
  val f_let   : (form * a_let  ) -> a_let   -> form
  val f_op    : (form * a_op   ) -> a_op    -> form
  val f_tuple : (form * a_tuple) -> a_tuple -> form
  val f_app   : (form * a_app  ) -> a_app   -> form
end

(* -------------------------------------------------------------------- *)
(* WARNING : this function should be use only in a context ensuring
 * that the quantified variables can be instanciated *)

val f_if_simpl   : form -> form -> form -> form
val f_let_simpl  : EcTypes.lpattern -> form -> form -> form
val f_lets_simpl : (EcTypes.lpattern * form) list -> form -> form

val f_forall_simpl  : binding -> form -> form
val f_exists_simpl  : binding -> form -> form
val f_app_simpl     : form -> form list -> EcTypes.ty -> form
val f_betared_simpl : binding -> form -> form list -> EcTypes.ty -> form

val f_not_simpl  : form -> form
val f_and_simpl  : form -> form -> form
val f_ands_simpl : form list -> form -> form
val f_anda_simpl : form -> form -> form
val f_or_simpl   : form -> form -> form
val f_ora_simpl  : form -> form -> form
val f_imp_simpl  : form -> form -> form
val f_imps       : form list -> form -> form
val f_imps_simpl : form list -> form -> form
val f_iff_simpl  : form -> form -> form
val f_eq_simpl   : form -> form -> form

val f_real_sum_simpl  : form -> form -> form
val f_real_prod_simpl : form -> form -> form
val f_real_div_simpl  : form -> form -> form

(* -------------------------------------------------------------------- *)
exception DestrError of string

val destr_local     : form -> EcIdent.t 
val destr_tuple     : form -> form list
val destr_not       : form -> form
val destr_and       : form -> form * form
val destr_or        : form -> form * form
val destr_or_kind   : form -> bool * form * form (* true asym *)
val destr_imp       : form -> form * form
val destr_iff       : form -> form * form
val destr_eq        : form -> form * form
val destr_eq_or_iff : form -> form * form
val destr_let1      : form -> EcIdent.t * ty * form * form
val destr_forall1   : form -> EcIdent.t * gty * form
val destr_forall    : form -> binding * form
val decompose_forall: form -> binding * form 
val destr_exists1   : form -> EcIdent.t * gty * form
val destr_exists    : form -> binding * form
val destr_equivF    : form -> equivF
val destr_equivS    : form -> equivS
val destr_hoareF    : form -> hoareF
val destr_hoareS    : form -> hoareS
val destr_bdHoareF  : form -> bdHoareF
val destr_bdHoareS  : form -> bdHoareS
val destr_pr        : form -> memory * EcPath.xpath * form list * form (* hr *) 
val destr_programS  : bool option -> form -> memenv * stmt

val is_true     : form -> bool
val is_false    : form -> bool
val is_tuple    : form -> bool
val is_not      : form -> bool
val is_and      : form -> bool
val is_or       : form -> bool
val is_imp      : form -> bool
val is_iff      : form -> bool
val is_forall   : form -> bool
val is_exists   : form -> bool
val is_let      : form -> bool
val is_eq       : form -> bool
val is_local    : form -> bool 
val is_equivF   : form -> bool
val is_equivS   : form -> bool
val is_hoareF   : form -> bool
val is_hoareS   : form -> bool
val is_bdHoareF : form -> bool
val is_bdHoareS : form -> bool
val is_pr       : form -> bool

val is_eq_or_iff : form -> bool

(* -------------------------------------------------------------------- *)
val f_map : (EcTypes.ty -> EcTypes.ty) -> (form -> form) -> form -> form

(* -------------------------------------------------------------------- *)
type f_subst = private { 
  fs_freshen : bool; (* true means realloc local *)
  fs_mp      : EcPath.mpath Mid.t;
  fs_loc     : form Mid.t;
  fs_mem     : EcIdent.t Mid.t;
  fs_sty     : ty_subst;
  fs_ty      : ty -> ty;
}

module Fsubst : sig
  val f_subst_id  : f_subst
  val is_subst_id : f_subst -> bool

  val f_subst_init : bool -> EcPath.mpath Mid.t -> ty_subst -> f_subst

  val f_bind_local : f_subst -> EcIdent.t -> form -> f_subst
  val f_bind_mem   : f_subst -> EcIdent.t -> EcIdent.t -> f_subst
  val f_bind_mod   : f_subst -> EcIdent.t -> EcPath.mpath -> f_subst

  val gty_subst : f_subst -> gty -> gty
  val f_subst   : f_subst -> form -> form 

  val f_subst_local : EcIdent.t -> form -> form -> form 
  val f_subst_mem   : EcIdent.t -> EcIdent.t -> form -> form 
  val f_subst_mod   : EcIdent.t -> EcPath.mpath -> form -> form 

  val uni : EcTypes.ty EcUidgen.Muid.t -> form -> form
  val subst_tvar : EcTypes.ty EcIdent.Mid.t -> form -> form
end

(* Checks that the input formula does not contain any unification variables *)
val f_check_uni : form -> bool

(* -------------------------------------------------------------------- *)
val form_of_expr : EcMemory.memory -> EcTypes.expr -> form

type op_kind = 
  | OK_true
  | OK_false
  | OK_not
  | OK_and   of bool  (* true = asym *)
  | OK_or    of bool  (* true = asym *)
  | OK_imp
  | OK_iff
  | OK_eq
  | OK_other 

val op_kind       : EcPath.path -> op_kind
val is_logical_op : EcPath.path -> bool

val is_op_and : EcPath.path -> bool
val is_op_or  : EcPath.path -> bool

(* -------------------------------------------------------------------- *)
(* Structured formulas - allows to get more information on the top-level
 * structure of a formula via direct pattern matching *)

type sform =
  | SFint   of int
  | SFlocal of EcIdent.t
  | SFpvar  of EcTypes.prog_var * memory
  | SFglob  of EcPath.mpath * memory 

  | SFif    of form * form * form
  | SFlet   of lpattern * form * form
  | SFtuple of form list

  | SFquant of quantif * (EcIdent.t * gty) * form
  | SFtrue
  | SFfalse
  | SFnot   of form
  | SFand   of bool * (form * form)
  | SFor    of bool * (form * form)
  | SFimp   of form * form
  | SFiff   of form * form
  | SFeq    of form * form
  | SFop    of (EcPath.path * ty list) * (form list)

  | SFhoareF   of hoareF
  | SFhoareS   of hoareS
  | SFbdHoareF of bdHoareF
  | SFbdHoareS of bdHoareS
  | SFequivF   of equivF
  | SFequivS   of equivS
  | SFpr       of pr

  | SFother of form

val sform_of_form : form -> sform
