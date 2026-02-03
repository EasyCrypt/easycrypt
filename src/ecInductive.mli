(* -------------------------------------------------------------------- *)
open EcUtils
open EcSymbols
open EcPath
open EcTypes
open EcCoreFol
open EcDecl

(* -------------------------------------------------------------------- *)
type field  = symbol * EcTypes.ty
type fields = field list

type record = {
  rc_path    : path;
  rc_tparams : ty_params;
  rc_fields  : fields;
}

(* -------------------------------------------------------------------- *)
type ctor  = symbol * (EcTypes.ty list)
type ctors = ctor list

type datatype = {
  dt_path    : path;
  dt_tparams : ty_params;
  dt_ctors   : ctors
}

(* -------------------------------------------------------------------- *)
val record_ctor_name : symbol -> symbol
val record_ind_path  : symbol -> symbol

val record_ctor_path : path -> path
val record_ind_path  : path -> path

(* -------------------------------------------------------------------- *)
val indsc_of_record : record -> form

(* -------------------------------------------------------------------- *)
val datatype_ind_name  : [`Elim|`Case] -> symbol -> symbol
val datatype_ind_path  : [`Elim|`Case] -> path   -> path
val datatype_proj_name : symbol -> symbol
val datatype_proj_path : path -> symbol -> path

(* -------------------------------------------------------------------- *)
type non_positive_intype = Concrete | Record of symbol | Variant of symbol

type non_positive_description =
  | InType of EcIdent.ident option * non_positive_intype
  | NonPositiveOcc of ty
  | AbstractTypeRestriction
  | TypePositionRestriction of ty

type non_positive_context = (symbol * non_positive_description) list

exception NonPositive of non_positive_context

val check_positivity : (path -> tydecl) -> datatype -> unit
(** Evaluates whether a given datatype protype satisfies the strict
    positivity check. The first argument defines how to retrieve the
    effective definition of a type constructor from its path.

    raises the exception [NonPositive] if the check fails, otherwise
    the function returns a unit value. *)

val indsc_of_datatype : ?normty:(ty -> ty) -> [`Elim|`Case] -> datatype -> form

val datatype_as_ty_dtype : datatype -> ty_params * ty_dtype
(* -------------------------------------------------------------------- *)
val datatype_projectors :
  path * ty_params * ty_dtype -> (symbol * operator) list

(* -------------------------------------------------------------------- *)
val datatype_projectors :
  path * ty_params * ty_dtype -> (symbol * operator) list

(* -------------------------------------------------------------------- *)
type case1 = {
  cs1_ctor : EcPath.path;
  cs1_vars : (EcIdent.t * EcTypes.ty) list;
}

type branch1 = {
  br1_target : EcIdent.t;
  br1_case   : case1;
}

type branch = {
  br_branches : branch1 list;
  br_body     : expr;
}

type opfix = branch list

(* -------------------------------------------------------------------- *)
val collate_matchfix  : EcDecl.opfix -> opfix

(* -------------------------------------------------------------------- *)
type prind = {
  ip_path    : path;
  ip_tparams : ty_params;
  ip_prind   : EcDecl.prind;
}

val indsc_of_prind : prind -> ty_params * form
val introsc_of_prind : prind -> (symbol * (ty_params * form)) list
val prind_schemes : prind -> (symbol * (ty_params * form)) list

val prind_indsc_name : symbol -> symbol
val prind_indsc_path : path -> path
val prind_introsc_path : path -> symbol -> path

val prind_is_iso_ands : EcDecl.prind -> (symbol * int) option
val prind_is_iso_ors : EcDecl.prind -> (symbol * int) pair option
