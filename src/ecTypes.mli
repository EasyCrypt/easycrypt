(* -------------------------------------------------------------------- *)
open EcBigInt
open EcMaps
open EcSymbols
open EcIdent

(* -------------------------------------------------------------------- *)
(* FIXME: section: move me *)

type locality  = [`Declare | `Local | `Global ]
type is_local  =           [ `Local | `Global ]

val local_of_locality : locality -> is_local

(* -------------------------------------------------------------------- *)
type ty = EcAst.ty
type ty_node = EcAst.ty_node

module Mty : Map.S with type key = ty
module Sty : Set.S with module M = Map.MakeBase(Mty)
module Hty : EcMaps.EHashtbl.S with type key = ty

type dom = ty list

val dump_ty : ty -> string

val ty_equal : ty -> ty -> bool
val ty_hash  : ty -> int

val tuni    : EcUid.uid -> ty
val tvar    : EcIdent.t -> ty
val ttuple  : ty list -> ty
val tconstr : EcPath.path -> ty list -> ty
val tfun    : ty -> ty -> ty
val tglob   : EcIdent.t -> ty
val tpred   : ty -> ty

val ty_fv_and_tvar : ty -> int Mid.t

(* -------------------------------------------------------------------- *)
val tunit   : ty
val tbool   : ty
val tint    : ty
val txint   : ty
val treal   : ty
val tdistr  : ty -> ty
val toption : ty -> ty
val tcpred  : ty -> ty
val toarrow : ty list -> ty -> ty

val trealp : ty
val txreal : ty

val tytuple_flat : ty -> ty list
val tyfun_flat   : ty -> (dom * ty)

(* -------------------------------------------------------------------- *)
val is_tdistr : ty -> bool
val as_tdistr : ty -> ty option

(* -------------------------------------------------------------------- *)
exception FoundUnivar

val ty_check_uni : ty -> unit

(* -------------------------------------------------------------------- *)

module Tvar : sig
  val fv      : ty -> Sid.t
end

(* -------------------------------------------------------------------- *)
(* [map f t] applies [f] on strict subterms of [t] (not recursive) *)
val ty_map : (ty -> ty) -> ty -> ty

(* [sub_exists f t] true if one of the strict-subterm of [t] valid [f] *)
val ty_sub_exists : (ty -> bool) -> ty -> bool

val ty_fold : ('a -> ty -> 'a) -> 'a -> ty -> 'a
val ty_iter : (ty -> unit) -> ty -> unit

val var_mem : ?check_glob:bool -> EcIdent.t -> ty -> bool

(* -------------------------------------------------------------------- *)
val symbol_of_ty   : ty -> string
val fresh_id_of_ty : ty -> EcIdent.t

(* -------------------------------------------------------------------- *)
type lpattern = EcAst.lpattern

val lp_equal : lpattern -> lpattern -> bool
val lp_hash  : lpattern -> int
val lp_bind  : lpattern -> (EcIdent.t * ty) list
val lp_ids   : lpattern -> EcIdent.t list
val lp_fv    : lpattern -> EcIdent.Sid.t

(* -------------------------------------------------------------------- *)
type ovariable = EcAst.ovariable

val ov_name  : ovariable -> symbol option
val ov_type  : ovariable -> ty
val ov_hash  : ovariable -> int
val ov_equal : ovariable -> ovariable -> bool

type variable = EcAst.variable

val v_name  : variable -> symbol
val v_type  : variable -> ty
val v_hash  : variable -> int
val v_equal : variable -> variable -> bool

val ovar_of_var: variable -> ovariable

(* -------------------------------------------------------------------- *)
type pvar_kind = EcAst.pvar_kind

type prog_var = EcAst.prog_var

val pv_equal       : prog_var -> prog_var -> bool
val pv_compare     : prog_var -> prog_var -> int
val pv_ntr_compare : prog_var -> prog_var -> int

val pv_kind : prog_var -> pvar_kind

(* work only if the prog_var has been normalized *)
val pv_compare_p : prog_var -> prog_var -> int
val pv_hash    : prog_var -> int
val pv_fv      : prog_var -> int EcIdent.Mid.t
val is_loc     : prog_var -> bool
val is_glob    : prog_var -> bool

val get_loc     : prog_var -> EcSymbols.symbol
val get_glob    : prog_var -> EcPath.xpath

val symbol_of_pv   : prog_var -> symbol
val string_of_pvar : prog_var -> string
val name_of_pvar   : prog_var -> string

val pv_subst : (EcPath.xpath -> EcPath.xpath) -> prog_var -> prog_var

val pv_loc  : EcSymbols.symbol -> prog_var
val pv_glob : EcPath.xpath -> prog_var
val xp_glob : EcPath.xpath -> EcPath.xpath

val arg_symbol : symbol
val res_symbol : symbol
val pv_res  : prog_var
val pv_arg  : prog_var

(* -------------------------------------------------------------------- *)
type expr = EcAst.expr
type expr_node = EcAst.expr_node

type equantif  = EcAst.equantif
type ebinding  = EcAst.ebinding
type ebindings = EcAst.ebindings

type closure = (EcIdent.t * ty) list * expr

(* -------------------------------------------------------------------- *)
val eqt_equal : equantif -> equantif -> bool

(* -------------------------------------------------------------------- *)
val e_equal   : expr -> expr -> bool
val e_compare : expr -> expr -> int
val e_hash    : expr -> int
val e_fv      : expr -> int EcIdent.Mid.t
val e_ty      : expr -> ty

(* -------------------------------------------------------------------- *)
val e_tt       : expr
val e_int      : zint -> expr
val e_decimal  : zint * (int * zint) -> expr
val e_local    : EcIdent.t -> ty -> expr
val e_var      : prog_var -> ty -> expr
val e_op       : EcPath.path -> ty list -> ty -> expr
val e_app      : expr -> expr list -> ty -> expr
val e_let      : lpattern -> expr -> expr -> expr
val e_tuple    : expr list -> expr
val e_if       : expr -> expr -> expr -> expr
val e_match    : expr -> expr list -> ty -> expr
val e_lam      : (EcIdent.t * ty) list -> expr -> expr
val e_quantif  : equantif -> ebindings -> expr -> expr
val e_forall   : ebindings -> expr -> expr
val e_exists   : ebindings -> expr -> expr
val e_proj     : expr -> int -> ty -> expr
val e_none     : ty -> expr
val e_some     : expr -> expr
val e_oget     : expr -> ty -> expr

val e_proj_simpl : expr -> int -> ty -> expr

(* -------------------------------------------------------------------- *)
module Me : Map.S with type key = expr
module Se : Set.S with module M = Map.MakeBase(Me)
module He : EcMaps.EHashtbl.S with type key = expr

(* -------------------------------------------------------------------- *)
val is_local     : expr -> bool
val is_var       : expr -> bool
val is_tuple_var : expr -> bool

val destr_local     : expr -> EcIdent.t
val destr_var       : expr -> prog_var
val destr_app       : expr -> expr * expr list
val destr_tuple_var : expr -> prog_var list

(* -------------------------------------------------------------------- *)
val split_args : expr -> expr * expr list

(* -------------------------------------------------------------------- *)
val e_map :
     (ty   -> ty  ) (* 1-subtype op. *)
  -> (expr -> expr) (* 1-subexpr op. *)
  -> expr
  -> expr

val e_fold :
  ('state -> expr -> 'state) -> 'state -> expr -> 'state

val e_iter : (expr -> unit) -> expr -> unit

(* -------------------------------------------------------------------- *)
