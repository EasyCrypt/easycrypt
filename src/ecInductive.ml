(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2015 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-C license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcUtils
open EcSymbols
open EcTypes
open EcDecl

module EP = EcPath

(* -------------------------------------------------------------------- *)
type field  = symbol * EcTypes.ty
type fields = field list

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

(* -------------------------------------------------------------------- *)
type ctor  = symbol * (EcTypes.ty list)
type ctors = ctor list

type datatype = {
  dt_path    : EcPath.path;
  dt_tparams : ty_params;
  dt_ctors   : ctors
}

(* -------------------------------------------------------------------- *)
type indmode = [`Elim | `Case]

let datatype_ind_name (mode : indmode) (x : symbol) =
  match mode with
  | `Elim -> Printf.sprintf "%s_ind"  x
  | `Case -> Printf.sprintf "%s_case" x

let datatype_ind_path (mode : indmode) (p : EcPath.path) =
  let name = datatype_ind_name mode (EcPath.basename p) in
  EcPath.pqoname (EcPath.prefix p) name

(* -------------------------------------------------------------------- *)
exception NonPositive

let indsc_of_datatype ?normty (mode : indmode) (dt : datatype) =
  let normty = odfl (identity : ty -> ty) normty in
  let tpath  = dt.dt_path in

  let rec scheme1 p (pred, fac) ty =
    match (normty ty).ty_node with
    | Tglob   _ -> assert false
    | Tunivar _ -> assert false
    | Tvar    _ -> None

    | Ttuple tys -> begin
        let xs  = List.map (fun xty -> (fresh_id_of_ty xty, xty)) tys in
        let sc1 = fun (x, xty) -> scheme1 p (pred, EcFol.f_local x xty) xty in
          match List.pmap sc1 xs with
          | []  -> None
          | scs -> Some (EcFol.f_let (LTuple xs) fac (EcFol.f_ands scs))
    end

    | Tconstr (p', ts)  ->
        if List.exists (occurs p) ts then raise NonPositive;
        if not (EcPath.p_equal p p') then None else
          Some (EcFol.f_app pred [fac] tbool)

    | Tfun (ty1, ty2) ->
        if occurs p ty1 then raise NonPositive;
        let x = fresh_id_of_ty ty1 in
          scheme1 p (pred, EcFol.f_app fac [EcFol.f_local x ty1] ty2) ty2
            |> omap (EcFol.f_forall [x, EcFol.GTty ty1])

  and schemec mode (targs, p) pred (ctor, tys) =
    let indty = tconstr p (List.map tvar targs) in
    let xs    = List.map (fun xty -> (fresh_id_of_ty xty, xty)) tys in
    let cargs = List.map (fun (x, xty) -> EcFol.f_local x xty) xs in
    let ctor  = EcPath.pqoname (EcPath.prefix tpath) ctor in
    let ctor  = EcFol.f_op ctor (List.map tvar targs) (toarrow tys indty) in
    let form  = EcFol.f_app pred [EcFol.f_app ctor cargs indty] tbool in
    let form  =
      match mode with
      | `Case -> form

      | `Elim ->
          let sc1 = fun (x, xty) -> scheme1 p (pred, EcFol.f_local x xty) xty in
          let scs = List.pmap sc1 xs in
            (EcFol.f_imps scs form)
    in

    let form  =
      let bds = List.map (fun (x, xty) -> (x, EcFol.GTty xty)) xs in
        EcFol.f_forall bds form

    in
      form

  and scheme mode (targs, p) ctors =
    let indty  = tconstr p (List.map tvar targs) in
    let indx   = fresh_id_of_ty indty in
    let indfm  = EcFol.f_local indx indty in
    let predty = tfun indty tbool in
    let predx  = EcIdent.create "P" in
    let pred   = EcFol.f_local predx predty in
    let scs    = List.map (schemec mode (targs, p) pred) ctors in
    let form   = EcFol.f_app pred [indfm] tbool in
    let form   = EcFol.f_forall [indx, EcFol.GTty indty] form in
    let form   = EcFol.f_imps scs form in
    let form   = EcFol.f_forall [predx, EcFol.GTty predty] form in
      form

  and occurs p t =
    match (normty t).ty_node with
    | Tconstr (p', _) when EcPath.p_equal p p' -> true
    | _ -> EcTypes.ty_sub_exists (occurs p) t

  in scheme mode (List.map fst dt.dt_tparams, tpath) dt.dt_ctors
