(* -------------------------------------------------------------------- *)
open EcUtils
open EcSymbols
open EcBigInt
open EcPath
open EcTypes
open EcCoreFol

(* -------------------------------------------------------------------- *)
type ty_param  = EcIdent.t * EcPath.Sp.t
type ty_params = ty_param list
type ty_pctor  = [ `Int of int | `Named of ty_params ]

type tydecl = {
  tyd_params   : ty_params;
  tyd_type     : ty_body;
  tyd_loca     : locality;
  tyd_clinline : bool;
}

and ty_body = [
  | `Concrete of EcTypes.ty
  | `Abstract of Sp.t
  | `Datatype of ty_dtype
  | `Record   of ty_record
]

and ty_record =
  EcCoreFol.form * (EcSymbols.symbol * EcTypes.ty) list

and ty_dtype_ctor =
  EcSymbols.symbol * EcTypes.ty list

and ty_dtype = {
  tydt_ctors   : ty_dtype_ctor list;
  tydt_schelim : EcCoreFol.form;
  tydt_schcase : EcCoreFol.form;
}

val tydecl_as_concrete : tydecl -> EcTypes.ty option
val tydecl_as_abstract : tydecl -> Sp.t option
val tydecl_as_datatype : tydecl -> ty_dtype option
val tydecl_as_record   : tydecl -> (form * (EcSymbols.symbol * EcTypes.ty) list) option

val abs_tydecl : ?tc:Sp.t -> ?params:ty_pctor -> locality -> tydecl

val ty_instanciate : ty_params -> ty list -> ty -> ty

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
  | OP_TC

and prbody =
  | PR_Plain of form
  | PR_Ind   of prind

and opfix = {
  opf_recp     : EcPath.path;
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

(* -------------------------------------------------------------------- *)
type axiom_kind = [`Axiom of (Ssym.t * bool) | `Lemma]

type axiom = {
  ax_tparams : ty_params;
  ax_spec    : form;
  ax_kind    : axiom_kind;
  ax_loca    : locality;
  ax_smt     : bool;
}

(* -------------------------------------------------------------------- *)
val is_axiom  : axiom_kind -> bool
val is_lemma  : axiom_kind -> bool

(* -------------------------------------------------------------------- *)
val axiomatized_op :
     ?nargs: int
  -> ?nosmt:bool
  -> EcPath.path
  -> (ty_params * form)
  -> locality
  -> axiom

(* -------------------------------------------------------------------- *)
type typeclass = {
  tc_prt : EcPath.path option;
  tc_ops : (EcIdent.t * EcTypes.ty) list;
  tc_axs : (EcSymbols.symbol * form) list;
  tc_loca: is_local;
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

(* -------------------------------------------------------------------- *)
type binding_size = form * (int option)

type crb_bitstring =
  { type_  : EcPath.path
  ; from_  : EcPath.path
  ; to_    : EcPath.path
  ; ofint  : EcPath.path
  ; touint : EcPath.path
  ; tosint : EcPath.path
  ; size   : binding_size
  ; theory : EcPath.path }
  
type crb_array =
  { type_  : EcPath.path
  ; get    : EcPath.path
  ; set    : EcPath.path
  ; tolist : EcPath.path
  ; oflist : EcPath.path
  ; size   : binding_size
  ; theory : EcPath.path }
  
type bv_opkind = [
  | `Add      of binding_size (* size *)
  | `Sub      of binding_size (* size *)
  | `Mul      of binding_size (* size *)
  | `Div      of binding_size * bool (* size + sign *)
  | `Rem      of binding_size * bool (* size + sign *)
  | `Shl      of binding_size (* size *)
  | `Shr      of binding_size * bool (* size + sign *)
  | `Shls     of binding_size * binding_size (* size *)
  | `Shrs     of binding_size * binding_size * bool (* size + sign *)
  | `Rol      of binding_size (* size *)
  | `Rol      of binding_size (* size *)
  | `Ror      of binding_size (* size *)
  | `And      of binding_size (* size *)
  | `Or       of binding_size (* size *)
  | `Xor      of binding_size (* size *)
  | `Not      of binding_size (* size *)
  | `Opp      of binding_size (* size *)
  | `Lt       of binding_size * bool (* size + sign *) 
  | `Le       of binding_size * bool (* size + sign *)
  | `Extend   of binding_size * binding_size * bool (* size in + size out + sign *)
  | `Truncate of binding_size * binding_size (* size in + size out *)
  | `Extract  of binding_size * binding_size (* size in + size out *)
  | `Insert   of binding_size * binding_size (* size in + size out *)
  | `Concat   of binding_size * binding_size * binding_size (* size in1 + size in2 *)
  | `Init     of binding_size (* size_out *)
  | `Get      of binding_size (* size_in *)
  | `AInit    of binding_size * binding_size (* arr_len + size_out *)
  | `Map      of binding_size * binding_size * binding_size (* size_in + size_out + arr_size *)
  | `A2B      of (binding_size * binding_size) * binding_size (* (arr_len, elem_sz), out_size *)
  | `B2A      of binding_size * (binding_size * binding_size) (* size in, (arr_len, elem_sz)  *)
  | `ASliceGet of (binding_size * binding_size) * binding_size (* arr_len + el_sz + sz_out *)
  | `ASliceSet of (binding_size * binding_size) * binding_size (* arr_len + el_sz + sz_in *)
]
  
type crb_bvoperator =
  { kind     : bv_opkind
  ; types    : EcPath.path list
  ; operator : EcPath.path
  ; theory   : EcPath.path }
  
type crb_circuit =
{ name     : string
; circuit  : Lospecs.Ast.adef
; operator : EcPath.path }

type crbinding =
| CRB_Bitstring  of crb_bitstring
| CRB_Array      of crb_array
| CRB_BvOperator of crb_bvoperator
| CRB_Circuit    of crb_circuit
