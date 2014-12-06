(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2014 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-C license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcParsetree
open EcLocation
open EcSymbols
open EcUtils
open EcTypes
open EcDecl

module TT = EcTyping
module EI = EcInductive

(* -------------------------------------------------------------------- *)
type rcerror =
| RCE_TypeError        of TT.tyerror
| RCE_DuplicatedField  of symbol
| RCE_InvalidFieldType of symbol * TT.tyerror

type dterror =
| DTE_TypeError       of TT.tyerror
| DTE_DuplicatedCtor  of symbol
| DTE_InvalidCTorType of symbol * TT.tyerror
| DTE_NonPositive
| DTE_Empty

(* -------------------------------------------------------------------- *)
exception RcError of EcLocation.t * EcEnv.env * rcerror
exception DtError of EcLocation.t * EcEnv.env * dterror

(* -------------------------------------------------------------------- *)
let rcerror loc env e = raise (RcError (loc, env, e))
let dterror loc env e = raise (DtError (loc, env, e))

(* -------------------------------------------------------------------- *)
let pp_rcerror env fmt error =
  let msg x = Format.fprintf fmt x in

  match error with
  | RCE_TypeError ee ->
      TT.pp_tyerror env fmt ee

  | RCE_DuplicatedField name ->
      msg "duplicated field: `%s'" name

  | RCE_InvalidFieldType (name, ee) ->
      msg "invalid field type: `%s`: %a'" name (TT.pp_tyerror env) ee

(* -------------------------------------------------------------------- *)
let pp_dterror env fmt error =
  let msg x = Format.fprintf fmt x in

  match error with
  | DTE_TypeError ee ->
      TT.pp_tyerror env fmt ee

  | DTE_DuplicatedCtor name ->
      msg "duplicated constructor name: `%s'" name

  | DTE_InvalidCTorType (name, ee) ->
      msg "invalid constructor type: `%s`: %a'"
        name (TT.pp_tyerror env) ee

  | DTE_NonPositive ->
      msg "the datatype does not respect the positivity condition"

  | DTE_Empty ->
      msg "the datatype is empty"

(* -------------------------------------------------------------------- *)
let () =
  let pp fmt exn =
    match exn with
    | RcError (_, env, e) -> pp_rcerror env fmt e
    | DtError (_, env, e) -> pp_dterror env fmt e
    | _ -> raise exn

  in EcPException.register pp

(* -------------------------------------------------------------------- *)
let trans_record (env : EcEnv.env) (name : ptydname) (rc : precord) =
  let { pl_loc = loc; pl_desc = (tyvars, name); } = name in

  (* Check type-parameters *)
  let ue    = TT.transtyvars env (loc, Some tyvars) in
  let tpath = EcPath.pqname (EcEnv.root env) (unloc name) in

  (* Check for duplicated field names *)
  Msym.odup unloc (List.map fst rc) |> oiter (fun (x, y) ->
    rcerror y.pl_loc env (RCE_DuplicatedField x.pl_desc));

  (* Type-check field types *)
  let fields =
    let for1 (fname, fty) =
      try
        let fty = TT.transty TT.tp_tydecl env ue fty in
        (unloc fname, fty)
      with TT.TyError (loc, _, ee) ->
        rcerror loc env (RCE_InvalidFieldType (unloc fname, ee))
    in rc |> List.map for1
  in

  (* Create record *)
  let tparams = EcUnify.UniEnv.tparams ue in

  { EI.rc_path = tpath; EI.rc_tparams = tparams; EI.rc_fields = fields; }

(* -------------------------------------------------------------------- *)
let trans_datatype (env : EcEnv.env) (name : ptydname) (dt : pdatatype) =
  let { pl_loc = loc; pl_desc = (tyvars, name); } = name in

  (* Check type-parameters / env0 is the env. augmented with an
   * abstract type representing the currently processed datatype. *)
  let ue    = TT.transtyvars env (loc, Some tyvars) in
  let tpath = EcPath.pqname (EcEnv.root env) (unloc name) in
  let env0  =
    let myself = {
      tyd_params = EcUnify.UniEnv.tparams ue;
      tyd_type   = `Abstract EcPath.Sp.empty;
    } in
      EcEnv.Ty.bind (unloc name) myself env
  in

  (* Check for duplicated constructor names *)
  Msym.odup unloc (List.map fst dt) |> oiter (fun (x, y) ->
    dterror y.pl_loc env (DTE_DuplicatedCtor x.pl_desc));

  (* Type-check constructor types *)
  let ctors =
    let for1 (cname, cty) =
      let ue  = EcUnify.UniEnv.copy ue in
      let cty = cty |> List.map (TT.transty TT.tp_tydecl env0 ue) in
        (unloc cname, cty)
    in
      dt |> List.map for1
  in

  (* Check for emptyness *)
  begin
    let rec occurs p ty =
      match (EcEnv.Ty.hnorm ty env0).ty_node with
      | Tconstr (p', _) when EcPath.p_equal p p' -> true
      | _ -> EcTypes.ty_sub_exists (occurs p) ty

    in
    if List.for_all (fun (_, cty) -> List.exists (occurs tpath) cty) ctors then
      dterror loc env DTE_Empty;
  end;

  let tparams = EcUnify.UniEnv.tparams ue in

  { EI.dt_path = tpath; EI.dt_tparams = tparams; EI.dt_ctors = ctors; }
