(* -------------------------------------------------------------------- *)
open EcDebug
open EcMaps
open EcUtils
open EcSymbols
open EcParsetree
open EcUidgen
open EcIdent

(* -------------------------------------------------------------------- *)
type ty = private {
  ty_node : ty_node;
  ty_tag  : int 
}

and ty_node =
  | Tglob   of EcPath.mpath (* The tuple of global variable of the module *)
  | Tunivar of EcUidgen.uid
  | Tvar    of EcIdent.t 
  | Ttuple  of ty list
  | Tconstr of EcPath.path * ty list
  | Tfun    of ty * ty

type dom = ty list

val ty_equal : ty -> ty -> bool
val ty_hash  : ty -> int 

val tuni    : EcUidgen.uid -> ty
val tvar    : EcIdent.t -> ty
val ttuple  : ty list -> ty
val tconstr : EcPath.path -> ty list -> ty
val tfun    : ty -> ty -> ty
val tglob   : EcPath.mpath -> ty 

(* -------------------------------------------------------------------- *)
val tunit      : ty
val tbool      : ty
val tint       : ty
val treal      : ty
val tdistr     : ty -> ty
val toarrow    : ty list -> ty -> ty

(* -------------------------------------------------------------------- *)
val ty_dump  : ty -> EcDebug.dnode

(* -------------------------------------------------------------------- *)
type ty_subst = {
  ts_p  : EcPath.path -> EcPath.path;
  ts_mp : EcPath.mpath -> EcPath.mpath;
  ts_u  : ty Muid.t;
  ts_v  : ty Mid.t;
}

val ty_subst_id : ty_subst

val ty_subst : ty_subst -> ty -> ty

module Tuni : sig
  val subst1    : (uid * ty) -> ty -> ty
  val subst     : ty Muid.t -> ty -> ty
  val subst_dom : ty Muid.t -> dom -> dom
  val occur     : uid -> ty -> bool
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
type lpattern =
  | LSymbol of (EcIdent.t*ty)
  | LTuple  of (EcIdent.t*ty) list

val lp_equal : lpattern -> lpattern -> bool
val lp_hash  : lpattern -> int 
val lp_ids   : lpattern -> EcIdent.t list
val lp_fv    : lpattern -> EcIdent.Sid.t

(* -------------------------------------------------------------------- *)
type pvar_kind =
  | PVglob
  | PVloc

type prog_var = {
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

val string_of_pvar : prog_var -> string

val pv_subst : (EcPath.xpath -> EcPath.xpath) -> prog_var -> prog_var 

val pv_loc : EcPath.xpath -> symbol -> prog_var
val pv_res : EcPath.xpath -> prog_var

(* -------------------------------------------------------------------- *)
type expr = private {
  e_node : expr_node;
  e_ty   : ty;
  e_fv   : int Mid.t;    (* module idents, locals *)
  e_tag  : int;
}

and expr_node =
  | Elam   of (EcIdent.t * ty) list * expr (* lambda expression *)
  | Eint   of int                        (* int. literal          *)
  | Elocal of EcIdent.t                  (* let-variables         *)
  | Evar   of prog_var                   (* module variable       *)
  | Eop    of EcPath.path * ty list      (* op apply to type args *)
  | Eapp   of expr * expr list           (* op. application       *)
  | Elet   of lpattern * expr * expr     (* let binding           *)
  | Etuple of expr list                  (* tuple constructor     *)
  | Eif    of expr * expr * expr         (* _ ? _ : _             *)

val expr_dump   : expr -> dnode

(* -------------------------------------------------------------------- *)
val e_equal   : expr -> expr -> bool
val e_compare : expr -> expr -> int
val e_hash    : expr -> int
val e_fv      : expr -> int EcIdent.Mid.t
val e_ty      : expr -> ty

(* -------------------------------------------------------------------- *)
val e_int      : int -> expr
val e_local    : EcIdent.t -> ty -> expr
val e_var      : prog_var -> ty -> expr
val e_op       : EcPath.path -> ty list -> ty -> expr
val e_app      : expr -> expr list -> ty -> expr
val e_let      : lpattern -> expr -> expr -> expr
val e_tuple    : expr list -> expr
val e_if       : expr -> expr -> expr -> expr
val e_lam      : (EcIdent.t * ty) list -> expr -> expr
(* -------------------------------------------------------------------- *)
val e_map :
     (ty     -> ty    ) (* 1-subtype op. *)
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
    es_mp      : EcPath.mpath -> EcPath.mpath; 
    es_xp      : EcPath.xpath -> EcPath.xpath;
    es_loc     : expr Mid.t;
  }

val e_subst_id   : e_subst

val e_subst_init : 
    bool -> (EcPath.path -> EcPath.path) ->
      (ty -> ty) -> EcPath.mpath EcIdent.Mid.t -> e_subst

val add_locals   : e_subst -> 
  (EcIdent.t * ty) list -> e_subst * (EcIdent.t * ty) list

val e_subst : e_subst -> expr -> expr
val e_mapty : (ty -> ty) -> expr -> expr 
val e_uni   : ty Muid.t -> expr -> expr

(* -------------------------------------------------------------------- *)
module Dump : sig
  val ty_dump : EcDebug.ppdebug -> ty -> unit
  val ex_dump : EcDebug.ppdebug -> expr -> unit
end
