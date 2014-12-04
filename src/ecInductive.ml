(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2014 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-C license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcUtils
open EcSymbols
open EcTypes
open EcDecl

module EP = EcPath

(* -------------------------------------------------------------------- *)
type field  = symbol * ty
type fields = field list

(* -------------------------------------------------------------------- *)
type record = {
  rc_path    : EcPath.path;
  rc_tparams : ty_params;
  rc_fields  : fields;
}

(* -------------------------------------------------------------------- *)
let record_ctor_name (x : symbol) = Printf.sprintf "mk_%s"  x
let record_ind_name  (x : symbol) = Printf.sprintf "%s_ind" x

(* -------------------------------------------------------------------- *)
let record_ctor_path (p : EP.path) =
  EcPath.pqoname (EcPath.prefix p) (record_ctor_name (EcPath.basename p))

(* -------------------------------------------------------------------- *)
let record_ind_path (p : EP.path) =
  EcPath.pqoname (EcPath.prefix p) (record_ind_name (EcPath.basename p))

(* -------------------------------------------------------------------- *)
let indsc_of_record (rc : record) =
  let targs  = List.map (tvar |- fst) rc.rc_tparams in
  let recty  = tconstr rc.rc_path targs in
  let recx   = fresh_id_of_ty recty in
  let recfm  = EcFol.f_local recx recty in
  let predty = tfun recty tbool in
  let predx  = EcIdent.create "P" in
  let pred   = EcFol.f_local predx predty in
  let ctor   = record_ctor_path rc.rc_path in
  let ctor   = EcFol.f_op ctor targs (toarrow (List.map snd rc.rc_fields) recty) in
  let prem   =
    let ids  = List.map (fun (_, fty) -> (fresh_id_of_ty fty, fty)) rc.rc_fields in
    let vars = List.map (fun (x, xty) -> EcFol.f_local x xty) ids in
    let bds  = List.map (fun (x, xty) -> (x, EcFol.GTty xty)) ids in
    let recv = EcFol.f_app ctor vars recty in
    EcFol.f_forall bds (EcFol.f_app pred [recv] tbool) in
  let form   = EcFol.f_app pred [recfm] tbool in
  let form   = EcFol.f_forall [recx, EcFol.GTty recty] form in
  let form   = EcFol.f_imp prem form in
  let form   = EcFol.f_forall [predx, EcFol.GTty predty] form in

  form
