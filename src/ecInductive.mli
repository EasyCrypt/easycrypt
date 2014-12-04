(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2014 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-C license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcSymbols
open EcPath
open EcFol
open EcDecl

(* -------------------------------------------------------------------- *)
type field  = symbol * EcTypes.ty
type fields = field list

(* -------------------------------------------------------------------- *)
type record = {
  rc_path    : path;
  rc_tparams : ty_params;
  rc_fields  : fields;
}

(* -------------------------------------------------------------------- *)
val record_ctor_name : symbol -> symbol
val record_ind_path  : symbol -> symbol

val record_ctor_path : path -> path
val record_ind_path  : path -> path

(* -------------------------------------------------------------------- *)
val indsc_of_record : record -> form
