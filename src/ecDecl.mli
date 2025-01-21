(* -------------------------------------------------------------------- *)
open EcUtils
open EcAst
open EcSymbols
open EcBigInt
open EcTypes
open EcCoreFol

(* -------------------------------------------------------------------- *)
type ty_param  = EcIdent.t * typeclass list
type ty_params = ty_param list
type ty_pctor  = [ `Int of int | `Named of ty_params ]

type tydecl = {
  tyd_params  : ty_params;
  tyd_type    : ty_body;
  tyd_loca    : locality;
  tyd_resolve : bool;
}

and ty_body = [
  | `Concrete of EcTypes.ty
  | `Abstract of typeclass list
  | `Datatype of ty_dtype
  | `Record   of form * (EcSymbols.symbol * EcTypes.ty) list
]

and ty_dtype = {
  tydt_ctors   : (EcSymbols.symbol * EcTypes.ty list) list;
  tydt_schelim : form;
  tydt_schcase : form;
}

val tydecl_as_concrete : tydecl -> EcTypes.ty option
val tydecl_as_abstract : tydecl -> typeclass list option
val tydecl_as_datatype : tydecl -> ty_dtype option
val tydecl_as_record   : tydecl -> (form * (EcSymbols.symbol * EcTypes.ty) list) option

val abs_tydecl : ?resolve:bool -> ?tc:typeclass list -> ?params:ty_pctor -> locality -> tydecl

val etyargs_of_tparams : ty_params -> etyarg list

val ty_instanciate : ty_params -> etyarg list -> ty -> ty

(* -------------------------------------------------------------------- *)
type locals = EcIdent.t list

type operator_kind =
  | OB_oper of opbody option
  | OB_pred of prbody option
  | OB_nott of notation

and opbody =
  | OP_Plain  of EcCoreFol.form
  | OP_Constr of EcPath.path * int
  | OP_Record of EcPath.path
  | OP_Proj   of EcPath.path * int * int
  | OP_Fix    of opfix
  | OP_TC     of EcPath.path * string

and prbody =
  | PR_Plain of form
  | PR_Ind   of prind

and opfix = {
  opf_args     : (EcIdent.t * EcTypes.ty) list;
  opf_resty    : EcTypes.ty;
  opf_struct   : int list * int;
  opf_branches : opbranches;
}

and opbranches =
| OPB_Leaf   of ((EcIdent.t * EcTypes.ty) list) list * EcTypes.expr
| OPB_Branch of opbranch Parray.parray

and opbranch = {
  opb_ctor : EcPath.path * int;
  opb_sub  : opbranches;
}

and notation = {
  ont_args  : (EcIdent.t * EcTypes.ty) list;
  ont_resty : EcTypes.ty;
  ont_body  : expr;
  ont_ponly : bool;
}

and prind = {
  pri_args  : (EcIdent.t * EcTypes.ty) list;
  pri_ctors : prctor list;
}

and prctor = {
  prc_ctor : symbol;
  prc_bds  : (EcIdent.t * gty) list;
  prc_spec : form list;
}

type operator = {
  op_tparams  : ty_params;
  op_ty       : EcTypes.ty;
  op_kind     : operator_kind;
  op_loca     : locality;
  op_opaque   : opopaque;
  op_clinline : bool;
  op_unfold   : int option;
}

and opopaque = { smt: bool; reduction: bool; }

val op_ty     : operator -> ty
val is_pred   : operator -> bool
val is_oper   : operator -> bool
val is_ctor   : operator -> bool
val is_proj   : operator -> bool
val is_rcrd   : operator -> bool
val is_tc_op  : operator -> bool
val is_fix    : operator -> bool
val is_abbrev : operator -> bool
val is_prind  : operator -> bool

val optransparent : opopaque

val mk_op   : ?clinline:bool -> ?unfold:int -> opaque:opopaque -> ty_params -> ty -> opbody option -> locality -> operator
val mk_pred : ?clinline:bool -> ?unfold:int -> opaque:opopaque -> ty_params -> ty list -> prbody option -> locality -> operator

val mk_abbrev :
     ?ponly:bool -> ty_params -> (EcIdent.ident * ty) list
  -> ty * expr -> locality -> operator

val operator_as_ctor  : operator -> EcPath.path * int
val operator_as_rcrd  : operator -> EcPath.path
val operator_as_proj  : operator -> EcPath.path * int * int
val operator_as_fix   : operator -> opfix
val operator_as_prind : operator -> prind
val operator_as_tc    : operator -> EcPath.path * string

(* -------------------------------------------------------------------- *)
type axiom_kind = [`Axiom of (Ssym.t * bool) | `Lemma]

type axiom = {
  ax_tparams    : ty_params;
  ax_spec       : form;
  ax_kind       : axiom_kind;
  ax_loca       : locality;
  ax_visibility : ax_visibility;
}

and ax_visibility = [`Visible | `NoSmt | `Hidden]

(* -------------------------------------------------------------------- *)
val is_axiom  : axiom_kind -> bool
val is_lemma  : axiom_kind -> bool

(* -------------------------------------------------------------------- *)
type tc_decl = {
  tc_tparams : ty_params;
  tc_prt     : typeclass option;
  tc_ops     : (EcIdent.t * EcTypes.ty) list;
  tc_axs     : (EcSymbols.symbol * EcCoreFol.form) list;
  tc_loca    : is_local;
}

(* -------------------------------------------------------------------- *)
type rkind = [
  | `Boolean
  | `Integer
  | `Modulus of (zint option) pair
]

type ring = {
  r_type  : EcTypes.ty;
  r_zero  : EcPath.path;
  r_one   : EcPath.path;
  r_add   : EcPath.path;
  r_opp   : EcPath.path option;
  r_mul   : EcPath.path;
  r_exp   : EcPath.path option;
  r_sub   : EcPath.path option;
  r_embed : [ `Direct | `Embed of EcPath.path | `Default];
  r_kind  : rkind;
}

val ring_equal : ring -> ring -> bool

(* -------------------------------------------------------------------- *)
type field = {
  f_ring : ring;
  f_inv  : EcPath.path;
  f_div  : EcPath.path option;
}
val field_equal : field -> field -> bool
