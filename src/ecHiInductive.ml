(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2014 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-C license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcParsetree
open EcLocation
open EcSymbols
open EcUtils

module TT = EcTyping
module EI = EcInductive

(* -------------------------------------------------------------------- *)
type rcerror =
| RCE_TypeError        of TT.tyerror
| RCE_DuplicatedField  of symbol
| RCE_InvalidFieldType of symbol * TT.tyerror

exception RcError of EcLocation.t * EcEnv.env * rcerror

(* -------------------------------------------------------------------- *)
let rcerror loc env e = raise (RcError (loc, env, e))

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
let () =
  let pp fmt exn =
    match exn with
    | RcError (_, env, e) ->
        pp_rcerror env fmt e
    | _ -> raise exn
  in
    EcPException.register pp

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
