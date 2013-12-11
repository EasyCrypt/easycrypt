(* -------------------------------------------------------------------- *)
open EcMaps
open EcUtils
open EcSymbols
open EcParsetree
open EcUid
open EcIdent

(* -------------------------------------------------------------------- *)
type ty = private {
  ty_node : ty_node;
  ty_fv   : int Mid.t;
  ty_tag  : int 
}

and ty_node =
  | Tglob   of EcPath.mpath (* The tuple of global variable of the module *)
  | Tunivar of EcUid.uid
  | Tvar    of EcIdent.t 
  | Ttuple  of ty list
  | Tconstr of EcPath.path * ty list
  | Tfun    of ty * ty

module Mty : Map.S with type key = ty
module Sty : Set.S with module M = Map.MakeBase(Mty)
module Hty : EcMaps.EHashtbl.S with type key = ty

type dom = ty list

val ty_equal : ty -> ty -> bool
val ty_hash  : ty -> int 

val tuni    : EcUid.uid -> ty
val tvar    : EcIdent.t -> ty
val ttuple  : ty list -> ty
val tconstr : EcPath.path -> ty list -> ty
val tfun    : ty -> ty -> ty
val tglob   : EcPath.mpath -> ty 

(* -------------------------------------------------------------------- *)
val tunit   : ty
val tbool   : ty
val tint    : ty
val treal   : ty
val tdistr  : ty -> ty
val tfset   : ty -> ty
val tcpred  : ty -> ty
val toarrow : ty list -> ty -> ty

val flatten_ty : ty -> ty list

(* -------------------------------------------------------------------- *)
exception FoundUnivar

val ty_check_uni : ty -> unit

(* -------------------------------------------------------------------- *)
type ty_subst = {
  ts_p   : EcPath.path -> EcPath.path;
  ts_mp  : EcPath.mpath -> EcPath.mpath;
  ts_def : (EcIdent.t list * ty) EcPath.Mp.t;
  ts_u   : EcUid.uid -> ty option;
  ts_v   : EcIdent.t -> ty option;
}

val ty_subst_id    : ty_subst
val is_ty_subst_id : ty_subst -> bool

val ty_subst : ty_subst -> ty -> ty

module Tuni : sig
  val offun     : (uid -> ty option) -> ty  -> ty
  val offun_dom : (uid -> ty option) -> dom -> dom

  val subst1    : (uid * ty) -> ty -> ty
  val subst     : ty Muid.t -> ty -> ty
  val subst_dom : ty Muid.t -> dom -> dom
  val occurs    : uid -> ty -> bool
  val fv        : ty -> Suid.t
end

module Tvar : sig
  val subst1  : (EcIdent.t * ty) -> ty -> ty
  val subst   : ty Mid.t -> ty -> ty
  val init    : EcIdent.t list -> ty list -> ty Mid.t
  val fv      : ty -> Sid.t
end

(* -------------------------------------------------------------------- *)
(* [map f t] applies [f] on strict subterms of [t] (not recursive) *)
val ty_map : (ty -> ty) -> ty -> ty

(* [sub_exists f t] true if one of the strict-subterm of [t] valid [f] *)
val ty_sub_exists : (ty -> bool) -> ty -> bool

(* -------------------------------------------------------------------- *)
val symbol_of_ty   : ty -> string
val fresh_id_of_ty : ty -> EcIdent.t

(* -------------------------------------------------------------------- *)
type lpattern =
  | LSymbol of (EcIdent.t * ty)
  | LTuple  of (EcIdent.t * ty) list
  | LRecord of EcPath.path * (EcIdent.t option * ty) list

val lp_equal : lpattern -> lpattern -> bool
val lp_hash  : lpattern -> int 
val lp_bind  : lpattern -> (EcIdent.t * ty) list
val lp_ids   : lpattern -> EcIdent.t list
val lp_fv    : lpattern -> EcIdent.Sid.t

(* -------------------------------------------------------------------- *)
type pvar_kind =
  | PVglob
  | PVloc

type prog_var = private {
  pv_name : EcPath.xpath;
  pv_kind : pvar_kind;
}

val pv_equal   : prog_var -> prog_var -> bool 
val pv_compare : prog_var -> prog_var -> int
(* work only if the prog_var has been normalized *)
val pv_compare_p : prog_var -> prog_var -> int 
val pv_hash    : prog_var -> int
val pv_fv      : prog_var -> int EcIdent.Mid.t
val is_loc     : prog_var -> bool
val is_glob    : prog_var -> bool

val symbol_of_pv   : prog_var -> symbol
val string_of_pvar : prog_var -> string

val pv_subst : (EcPath.xpath -> EcPath.xpath) -> prog_var -> prog_var 

val pv_loc  : EcPath.xpath -> symbol -> prog_var
val pv_glob : EcPath.xpath -> prog_var 
val xp_glob : EcPath.xpath -> EcPath.xpath
val pv_res  : EcPath.xpath -> prog_var
val pv_arg  : EcPath.xpath -> prog_var
val pv      : EcPath.xpath -> pvar_kind -> prog_var

(* -------------------------------------------------------------------- *)
type expr = private {
  e_node : expr_node;
  e_ty   : ty;
  e_fv   : int Mid.t;    (* module idents, locals *)
  e_tag  : int;
}

and expr_node =
  | Elam   of (EcIdent.t * ty) list * expr (* lambda expression     *)
  | Eint   of int                          (* int. literal          *)
  | Elocal of EcIdent.t                    (* let-variables         *)
  | Evar   of prog_var                     (* module variable       *)
  | Eop    of EcPath.path * ty list        (* op apply to type args *)
  | Eapp   of expr * expr list             (* op. application       *)
  | Elet   of lpattern * expr * expr       (* let binding           *)
  | Etuple of expr list                    (* tuple constructor     *)
  | Eif    of expr * expr * expr           (* _ ? _ : _             *)
  | Eproj  of expr * int                   (* projection of a tuple *)

type closure = (EcIdent.t * ty) list * expr

(* -------------------------------------------------------------------- *)
val e_equal   : expr -> expr -> bool
val e_compare : expr -> expr -> int
val e_hash    : expr -> int
val e_fv      : expr -> int EcIdent.Mid.t
val e_ty      : expr -> ty

(* -------------------------------------------------------------------- *)
val e_tt       : expr
val e_int      : int -> expr
val e_local    : EcIdent.t -> ty -> expr
val e_var      : prog_var -> ty -> expr
val e_op       : EcPath.path -> ty list -> ty -> expr
val e_app      : expr -> expr list -> ty -> expr
val e_let      : lpattern -> expr -> expr -> expr
val e_tuple    : expr list -> expr
val e_if       : expr -> expr -> expr -> expr
val e_lam      : (EcIdent.t * ty) list -> expr -> expr
val e_proj     : expr -> int -> ty -> expr

val is_var     : expr -> bool
val destr_var  : expr -> prog_var 

val is_tuple_var    : expr -> bool
val destr_tuple_var : expr -> prog_var list

(* -------------------------------------------------------------------- *)
val e_map :
     (ty   -> ty  ) (* 1-subtype op. *)
  -> (expr -> expr) (* 1-subexpr op. *)
  -> expr
  -> expr

val e_fold :
  ('state -> expr -> 'state) -> 'state -> expr -> 'state

(* -------------------------------------------------------------------- *)
type e_subst = { 
  es_freshen : bool; (* true means realloc local *)
  es_p       : EcPath.path -> EcPath.path;
  es_ty      : ty -> ty;
  es_opdef   : (EcIdent.t list * expr) EcPath.Mp.t;
  es_mp      : EcPath.mpath -> EcPath.mpath; 
  es_xp      : EcPath.xpath -> EcPath.xpath;
  es_loc     : expr Mid.t;
}

val e_subst_id : e_subst

val e_subst_init : 
      bool
  -> (EcPath.path -> EcPath.path)
  -> (ty -> ty)
  -> (EcIdent.t list * expr) EcPath.Mp.t
  -> EcPath.mpath EcIdent.Mid.t
  -> e_subst

val add_local  : e_subst -> EcIdent.t * ty -> e_subst * (EcIdent.t * ty)
val add_locals : e_subst -> (EcIdent.t * ty) list -> e_subst * (EcIdent.t * ty) list

val e_subst_closure : e_subst -> closure -> closure
val e_subst : e_subst -> expr -> expr

val e_mapty : (ty -> ty) -> expr -> expr 
val e_uni   : (uid -> ty option) -> expr -> expr

(* -------------------------------------------------------------------- *)
(* projects 'a Distr type into 'a *)
val proj_distr_ty : ty -> ty

