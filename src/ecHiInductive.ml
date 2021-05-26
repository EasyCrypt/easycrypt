(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcParsetree
open EcLocation
open EcSymbols
open EcIdent
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
| RCE_Empty

type dterror =
| DTE_TypeError       of TT.tyerror
| DTE_DuplicatedCtor  of symbol
| DTE_InvalidCTorType of symbol * TT.tyerror
| DTE_NonPositive
| DTE_Empty

type fxerror =
| FXE_TypeError of EcTyping.tyerror
| FXE_EmptyMatch
| FXE_MatchParamsMixed
| FXE_MatchParamsDup
| FXE_MatchParamsUnk
| FXE_MatchNonLinear
| FXE_MatchDupBranches
| FXE_MatchPartial
| FXE_CtorUnk
| FXE_CtorAmbiguous
| FXE_CtorInvalidArity of (symbol * int * int)

(* -------------------------------------------------------------------- *)
exception RcError of EcLocation.t * EcEnv.env * rcerror
exception DtError of EcLocation.t * EcEnv.env * dterror
exception FxError of EcLocation.t * EcEnv.env * fxerror

(* -------------------------------------------------------------------- *)
let rcerror loc env e = raise (RcError (loc, env, e))
let dterror loc env e = raise (DtError (loc, env, e))
let fxerror loc env e = raise (FxError (loc, env, e))

(* -------------------------------------------------------------------- *)
let trans_record (env : EcEnv.env) (name : ptydname) (rc : precord) =
  let { pl_loc = loc; pl_desc = (tyvars, name); } = name in

  (* Check type-parameters *)
  let ue    = TT.transtyvars env (loc, Some tyvars) in
  let tpath = EcPath.pqname (EcEnv.root env) (unloc name) in

  (* Check for duplicated field names *)
  Msym.odup unloc (List.map fst rc) |> oiter (fun (x, y) ->
    rcerror y.pl_loc env (RCE_DuplicatedField x.pl_desc));

  (* Check for emptyness *)
  if List.is_empty rc then
    rcerror loc env RCE_Empty;

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
      tyd_params  = EcUnify.UniEnv.tparams ue;
      tyd_type    = `Abstract EcPath.Sp.empty;
      tyd_resolve = true;
    } in
      EcEnv.Ty.bind (unloc name) myself env
  in

  let tparams = EcUnify.UniEnv.tparams ue in

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
    let rec isempty_n (ctors : (ty list) list) =
      List.for_all isempty_1 ctors

    and isempty_1 (ctor : ty list) =
      List.exists isempty ctor

    and isempty (ty : ty) =
      match ty.ty_node with
      | Tglob   _ -> false
      | Tvar    _ -> false
      | Tunivar _ -> false

      | Ttuple tys      -> List.exists isempty tys
      | Tfun   (t1, t2) -> List.exists isempty [t1; t2]

      | Tconstr (p, args) ->
          isempty_dtype (args, p)

    and isempty_dtype (targs, tname) =
      if EcPath.p_equal tname tpath then true else

      let tdecl = EcEnv.Ty.by_path_opt tname env0
        |> ofdfl (EcDecl.abs_tydecl ~params:(`Named tparams)) in
      let tyinst () =
        fun ty -> ty_instanciate tdecl.tyd_params targs ty in

      match tdecl.tyd_type with
      | `Abstract _ ->
          List.exists isempty (targs)

      | `Concrete ty ->
          isempty_1 [tyinst () ty]

      | `Record (_, fields) ->
          isempty_1 (List.map (tyinst () |- snd) fields)

      | `Datatype dt ->
          isempty_n (List.map (List.map (tyinst ()) |- snd) dt.tydt_ctors)

    in

    if isempty_n (List.map snd ctors) then
      dterror loc env DTE_Empty;
  end;

  { EI.dt_path = tpath; EI.dt_tparams = tparams; EI.dt_ctors = ctors; }

(* -------------------------------------------------------------------- *)
module CaseMap : sig
  type t

  type locals = (EcIdent.t * ty) list

  val create  : EcPath.path list list -> t
  val add     : (int * locals) list -> expr -> t -> bool
  val resolve : t -> opbranches option
end = struct
  type locals = (EcIdent.t * ty) list

  type t = [
    | `Case of (EcPath.path * t) array
    | `Leaf of (locals list * expr) option ref
  ]

  let rec create (inds : EcPath.path list list) =
    match inds with
    | [] -> `Leaf (ref None)
    | ind :: inds ->
        let ind = Array.of_list ind in
          `Case (Array.map (fun x -> (x, create inds)) ind)

  let add bs e (m : t) =
    let r =
      List.fold_left
        (fun m (i, _) ->
           match m with
           | `Leaf _ -> assert false
           | `Case t ->
               assert (i >= 0 && i < Array.length t);
               snd t.(i))
        m bs
    in
      match r with
      | `Case _ -> assert false
      | `Leaf r -> begin
          match !r with
          | None   -> r := Some (List.map snd bs, e); true
          | Some _ -> false
      end

  let resolve =
    let module E = struct exception NotFull end in

    let rec resolve_r m =
      match m with
      | `Case t ->
          let for1 i =
            let (cp, bs) = snd_map resolve_r t.(i) in
              { opb_ctor = (cp, i); opb_sub = bs; }
          in
            OPB_Branch (Parray.init (Array.length t) for1)

      | `Leaf r -> begin
          match !r with
          | None -> raise E.NotFull
          | Some (x1, x2) -> OPB_Leaf (x1, x2)
      end
  in
    fun m ->
      try  Some (resolve_r m)
      with E.NotFull -> None
end

(* -------------------------------------------------------------------- *)
type matchfix_t =  {
  mf_name     : ident;
  mf_codom    : EcTypes.ty;
  mf_args     : (ident * EcTypes.ty) list;
  mf_recs     : int list;
  mf_branches : EcDecl.opbranches;
}

(* -------------------------------------------------------------------- *)
let trans_matchfix ?(close = true) env ue { pl_loc = loc; pl_desc = name } (bd, pty, pbs) =
  let codom     = TT.transty TT.tp_relax env ue pty in
  let env, args = TT.trans_binding env ue bd in
  let ty        = EcTypes.toarrow (List.map snd args) codom in
  let opname    = EcIdent.create name in
  let env       = EcEnv.Var.bind_local opname ty env in

  let mpty, pbsmap =
    let pbsmap =
      List.map (fun x ->
        let nms = (fun pop -> (unloc pop.pop_name, pop)) in
        let nms = List.map nms x.pop_patterns in
          (x.pop_body, Msym.of_list nms))
        pbs
    in
      match List.map snd pbsmap with
      | [] ->
          fxerror loc env FXE_EmptyMatch

      | nm :: nms ->
          if not (List.for_all (Msym.set_equal nm) nms) then
            fxerror loc env FXE_MatchParamsMixed;
          let argsmap =
            List.fold_lefti
              (fun m i (x, xty) -> Msym.add (EcIdent.name x) (i, x, xty) m)
              Msym.empty args
          in

          let _, mpty =
            Msym.fold_left
              (fun (seen, mpty) px _ ->
                 if Msym.mem px seen then
                   fxerror loc env FXE_MatchParamsDup;

                 match Msym.find_opt px argsmap with
                 | None -> fxerror loc env FXE_MatchParamsUnk
                 | Some (i, x, xty) -> (Ssym.add px seen, (i, x, xty) :: mpty))
              (Ssym.empty, []) nm
          in
            (mpty, pbsmap)
  in

  let branches =
    let pbs =
      let trans_b ((body, pbmap) : _ * pop_pattern Msym.t) =
        let trans1 ((_, x, xty) : _ * EcIdent.t * ty) =
          let pb     = oget (Msym.find_opt (EcIdent.name x) pbmap) in
          let filter = fun op -> EcDecl.is_ctor op in
          let PPApp ((cname, tvi), cargs) = pb.pop_pattern in
          let tvi = tvi |> omap (TT.transtvi env ue) in
          let cts = EcUnify.select_op ~filter tvi env (unloc cname) ue [] in

          match cts with
          | [] ->
              fxerror cname.pl_loc env FXE_CtorUnk

          | _ :: _ :: _ ->
              fxerror cname.pl_loc env FXE_CtorAmbiguous

          | [(cp, tvi), opty, subue, _] ->
              let ctor = oget (EcEnv.Op.by_path_opt cp env) in
              let (indp, ctoridx) = EcDecl.operator_as_ctor ctor in
              let indty = oget (EcEnv.Ty.by_path_opt indp env) in
              let ind = (EcDecl.tydecl_as_datatype indty).tydt_ctors in
              let ctorsym, ctorty = List.nth ind ctoridx in

              let args_exp = List.length ctorty in
              let args_got = List.length cargs in

              if args_exp <> args_got then
                fxerror cname.pl_loc env
                  (FXE_CtorInvalidArity (snd (unloc cname), args_exp, args_got));

              let cargs_lin = List.pmap (fun o -> omap unloc (unloc o)) cargs in

              if not (List.is_unique cargs_lin) then
                fxerror cname.pl_loc env (FXE_MatchNonLinear);

              EcUnify.UniEnv.restore ~src:subue ~dst:ue;

              let ctorty =
                let tvi = Some (EcUnify.TVIunamed tvi) in
                  fst (EcUnify.UniEnv.opentys ue indty.tyd_params tvi ctorty) in
              let pty = EcUnify.UniEnv.fresh ue in

              (try  EcUnify.unify env ue (toarrow ctorty pty) opty
               with EcUnify.UnificationFailure _ -> assert false);
              TT.unify_or_fail env ue pb.pop_name.pl_loc pty xty;

              let create o =
                EcIdent.create (omap_dfl unloc "_" o) in
              let pvars = List.map (create |- unloc) cargs in
              let pvars = List.combine pvars ctorty in

              (pb, (indp, ind, (ctorsym, ctoridx)), pvars)
        in

        let ptns = List.map trans1 mpty in
        let env  =
          List.fold_left (fun env (_, _, pvars) ->
            EcEnv.Var.bind_locals pvars env)
            env ptns
        in
            (ptns, TT.transexpcast env `InOp ue codom body)
      in
        List.map trans_b pbsmap
    in

    let inds = (fun (_, (indp, ind, _), _) -> (indp, ind)) in
    let inds = List.map inds (fst (oget (List.ohead pbs))) in
    let inds =
      List.map (fun (indp, ctors) ->
        List.map
          (fun (ctor, _) -> EcPath.pqoname (EcPath.prefix indp) ctor)
          ctors)
        inds
    in

    let casemap = CaseMap.create inds in

    List.iter
      (fun (ptns, be) ->
         let ptns = List.map (fun (_, (_, _, (_, ctor)), pvars) ->
           (ctor, pvars)) ptns
         in
           if not (CaseMap.add ptns be casemap) then
             fxerror loc env FXE_MatchDupBranches)
      pbs;

    match CaseMap.resolve casemap with
    | None   -> fxerror loc env FXE_MatchPartial
    | Some x -> x

  in

  let aout =
    if close then
      let uni      = Tuni.offun (EcUnify.UniEnv.assubst ue) in
      let tparams  = EcUnify.UniEnv.tparams ue in
      let codom    = uni codom in
      let opexpr   = EcPath.pqname (EcEnv.root env) name in
      let args     = List.map (snd_map uni) args in
      let opexpr   = e_op opexpr (List.map (tvar |- fst) tparams)
                       (toarrow (List.map snd args) codom) in
      let ebsubst  =
        let lcmap = Mid.add opname opexpr e_subst_id.es_loc in
        { e_subst_id with es_freshen = false; es_ty = uni; es_loc = lcmap; }
      in

      let branches =
        let rec uni_branches = function
          | OPB_Leaf (locals, e) ->
              OPB_Leaf (List.map (List.map (snd_map uni)) locals, e_subst ebsubst e)

          | OPB_Branch bs ->
            let for1 b =
              { opb_ctor = b.opb_ctor;
                opb_sub  = uni_branches b.opb_sub; }
            in
              OPB_Branch (Parray.map for1 bs)
        in
          uni_branches branches

      in { mf_name     = opname;
           mf_codom    = codom;
           mf_args     = args;
           mf_recs     = List.map proj3_1 mpty;
           mf_branches = branches; }

    else { mf_name     = opname;
           mf_codom    = codom;
           mf_args     = args;
           mf_recs     = List.map proj3_1 mpty;
           mf_branches = branches; }

  in (ty, aout)
