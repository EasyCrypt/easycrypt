(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2014 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-C license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcSymbols
open EcPath
open EcTypes
open EcFol
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
val datatype_ind_name : [`Elim|`Case] -> symbol -> symbol
val datatype_ind_path : [`Elim|`Case] -> path   -> path

(* -------------------------------------------------------------------- *)
exception NonPositive

val indsc_of_datatype : ?normty:(ty -> ty) -> [`Elim|`Case] -> datatype -> form
