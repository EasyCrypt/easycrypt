(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2015 - IMDEA Software Institute
 * Copyright (c) - 2012--2015 - Inria
 * 
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcUtils
open EcSymbols
open EcTypes
open EcDecl

module EP = EcPath
module FL = EcCoreFol

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
  let recfm  = FL.f_local recx recty in
  let predty = tfun recty tbool in
  let predx  = EcIdent.create "P" in
  let pred   = FL.f_local predx predty in
  let ctor   = record_ctor_path rc.rc_path in
  let ctor   = FL.f_op ctor targs (toarrow (List.map snd rc.rc_fields) recty) in
  let prem   =
    let ids  = List.map (fun (_, fty) -> (fresh_id_of_ty fty, fty)) rc.rc_fields in
    let vars = List.map (fun (x, xty) -> FL.f_local x xty) ids in
    let bds  = List.map (fun (x, xty) -> (x, FL.GTty xty)) ids in
    let recv = FL.f_app ctor vars recty in
    FL.f_forall bds (FL.f_app pred [recv] tbool) in
  let form   = FL.f_app pred [recfm] tbool in
  let form   = FL.f_forall [recx, FL.GTty recty] form in
  let form   = FL.f_imp prem form in
  let form   = FL.f_forall [predx, FL.GTty predty] form in

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
        let sc1 = fun (x, xty) -> scheme1 p (pred, FL.f_local x xty) xty in
          match List.pmap sc1 xs with
          | []  -> None
          | scs -> Some (FL.f_let (LTuple xs) fac (FL.f_ands scs))
    end

    | Tconstr (p', ts)  ->
        if List.exists (occurs p) ts then raise NonPositive;
        if not (EcPath.p_equal p p') then None else
          Some (FL.f_app pred [fac] tbool)

    | Tfun (ty1, ty2) ->
        if occurs p ty1 then raise NonPositive;
        let x = fresh_id_of_ty ty1 in
          scheme1 p (pred, FL.f_app fac [FL.f_local x ty1] ty2) ty2
            |> omap (FL.f_forall [x, FL.GTty ty1])

  and schemec mode (targs, p) pred (ctor, tys) =
    let indty = tconstr p (List.map tvar targs) in
    let xs    = List.map (fun xty -> (fresh_id_of_ty xty, xty)) tys in
    let cargs = List.map (fun (x, xty) -> FL.f_local x xty) xs in
    let ctor  = EcPath.pqoname (EcPath.prefix tpath) ctor in
    let ctor  = FL.f_op ctor (List.map tvar targs) (toarrow tys indty) in
    let form  = FL.f_app pred [FL.f_app ctor cargs indty] tbool in
    let form  =
      match mode with
      | `Case -> form

      | `Elim ->
          let sc1 = fun (x, xty) -> scheme1 p (pred, FL.f_local x xty) xty in
          let scs = List.pmap sc1 xs in
            (FL.f_imps scs form)
    in

    let form  =
      let bds = List.map (fun (x, xty) -> (x, FL.GTty xty)) xs in
        FL.f_forall bds form

    in
      form

  and scheme mode (targs, p) ctors =
    let indty  = tconstr p (List.map tvar targs) in
    let indx   = fresh_id_of_ty indty in
    let indfm  = FL.f_local indx indty in
    let predty = tfun indty tbool in
    let predx  = EcIdent.create "P" in
    let pred   = FL.f_local predx predty in
    let scs    = List.map (schemec mode (targs, p) pred) ctors in
    let form   = FL.f_app pred [indfm] tbool in
    let form   = FL.f_forall [indx, FL.GTty indty] form in
    let form   = FL.f_imps scs form in
    let form   = FL.f_forall [predx, FL.GTty predty] form in
      form

  and occurs p t =
    match (normty t).ty_node with
    | Tconstr (p', _) when EcPath.p_equal p p' -> true
    | _ -> EcTypes.ty_sub_exists (occurs p) t

  in scheme mode (List.map fst dt.dt_tparams, tpath) dt.dt_ctors

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
let collate_matchfix (fix : EcDecl.opfix) : opfix =
  let names = List.map
    (fun i -> fst (List.nth fix.opf_args i))
    (fst fix.opf_struct) in

  let rec collate ctors branches =
    match branches with
    | OPB_Leaf (vars, body) ->
        let branches =
          List.map2
            (fun br1_case br1_target -> { br1_target; br1_case; })
            (List.map2
               (fun cs1_ctor cs1_vars -> { cs1_ctor; cs1_vars; })
               ctors vars)
            names
        in [{ br_branches = branches; br_body = body }]

    | OPB_Branch br ->
        let aout =
          List.map
            (fun br1 -> collate (fst br1.opb_ctor :: ctors) br1.opb_sub)
            (Parray.to_list br)
        in List.flatten aout

  in collate [] fix.opf_branches

(*-------------------------------------------------------------------- *)
type prind = {
  ip_path    : EcPath.path;
  ip_tparams : ty_params;
  ip_prind   : EcDecl.prind;
}

(* -------------------------------------------------------------------- *)
let indsc_of_prind ({ ip_path = p; ip_prind = pri } as pr) =
  let bds   = List.map (snd_map FL.gtty) pri.pri_args in
  let prty  = toarrow (List.map snd pri.pri_args) tbool in
  let prag  = (List.map (curry FL.f_local) pri.pri_args) in
  let predx = EcIdent.create "P" in
  let pred  = FL.f_local predx tbool in

  let for1 ctor =
    let px = FL.f_imps ctor.prc_spec pred in
    FL.f_forall ctor.prc_bds px
  in

  let sc = FL.f_op p (List.map (tvar |- fst) pr.ip_tparams) prty in
  let sc = FL.f_imp (FL.f_app sc prag tbool) pred in
  let sc = FL.f_imps (List.map for1 pri.pri_ctors) sc in
  let sc = FL.f_forall [predx, FL.gtty tbool] sc in
  let sc = FL.f_forall bds sc in

  (pr.ip_tparams, sc)

(* -------------------------------------------------------------------- *)
let introsc_of_prind ({ ip_path = p; ip_prind = pri } as pr) =
  let bds  = List.map (snd_map FL.gtty) pri.pri_args in
  let clty = toarrow (List.map snd pri.pri_args) tbool in
  let clag = (List.map (curry FL.f_local) pri.pri_args) in
  let cl   = FL.f_op p (List.map (tvar |- fst) pr.ip_tparams) clty in
  let cl   = FL.f_app cl clag tbool in

  let for1 ctor =
    let cl = FL.f_imps ctor.prc_spec cl in
    let cl = FL.f_forall (bds @ ctor.prc_bds) cl in
    (pr.ip_tparams, cl)

  in List.map (fun c -> (c.prc_ctor, for1 c)) pri.pri_ctors

(* --------------------------------------------------------------------- *)
let prind_schemes (pr : prind) =
  ("ind", indsc_of_prind pr) :: (introsc_of_prind pr)

(* -------------------------------------------------------------------- *)
let prind_indsc_name (s : symbol) =
  Printf.sprintf "%s_ind" s 

let prind_indsc_path (p : EcPath.path) =
  EcPath.pqoname
    (EcPath.prefix p) (prind_indsc_name (EcPath.basename p))
