(* -------------------------------------------------------------------- *)
open EcParsetree
open EcLocation
open EcSymbols
open EcIdent
open EcUtils
open EcTypes
open EcCoreSubst
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
| DTE_NonPositive     of symbol * EI.non_positive_context
| DTE_Empty

type fxerror =
| FXLowError of EcTyping.tyerror
| FXError    of EcTyping.fxerror

(* -------------------------------------------------------------------- *)
exception RcError of EcLocation.t * EcEnv.env * rcerror
exception DtError of EcLocation.t * EcEnv.env * dterror
exception FxError of EcLocation.t * EcEnv.env * fxerror

(* -------------------------------------------------------------------- *)
let rcerror loc env e = raise (RcError (loc, env, e))
let dterror loc env e = raise (DtError (loc, env, e))
let fxerror loc env e = raise (FxError (loc, env, FXError e))

(* -------------------------------------------------------------------- *)
let trans_record (env : EcEnv.env) (name : ptydname) (rc : precord) =
  let { pl_loc = loc; pl_desc = (tyvars, name); } = name in

  (* Check type-parameters *)
  let ue    = TT.transtyvars env (loc, Some tyvars) in
  let tpath = EcPath.pqname (EcEnv.root env) (unloc name) in

  (* Check for duplicated field names *)
  Msym.odup unloc (List.map fst rc) |> oiter (fun (x, y) ->
    rcerror y.pl_loc env (RCE_DuplicatedField x.pl_desc));

  (* Check for emptiness *)
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
  let lc = `Global in
  let { pl_loc = loc; pl_desc = (tyvars, name); } = name in

  (* Check type-parameters / env0 is the env. augmented with an
   * abstract type representing the currently processed datatype. *)
  let ue    = TT.transtyvars env (loc, Some tyvars) in
  let tpath = EcPath.pqname (EcEnv.root env) (unloc name) in
  let env0  =
    let myself = {
      tyd_params  = EcUnify.UniEnv.tparams ue;
      tyd_type    = Abstract;
      tyd_loca    = lc;
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

  (* Check for emptiness *)
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
        |> odfl (EcDecl.abs_tydecl ~params:(`Named tparams) lc) in
      let tyinst = ty_instantiate tdecl.tyd_params targs in

      match tdecl.tyd_type with
      | Abstract ->
          List.exists isempty targs

      | Concrete ty ->
          isempty_1 [ tyinst ty ]

      | Record (_, fields) ->
          isempty_1 (List.map (tyinst -| snd) fields)

      | Datatype dt ->
          (* FIXME: Inspecting all constructors recursively causes
             non-termination in some cases. One can have the same
             limitation as is done for positivity in order to limit this
             unfolding to well-behaved cases. *)
          isempty_n (List.map (List.map tyinst -| snd) dt.tydt_ctors)

    in

    if isempty_n (List.map snd ctors) then
      dterror loc env DTE_Empty;
  end;

  { EI.dt_path = tpath; EI.dt_tparams = tparams; EI.dt_ctors = ctors; }

(* -------------------------------------------------------------------- *)
module CaseMap : sig
  type t

  type locals = (EcIdent.t * ty) list
  type pattern =
    | Single of int * EcPath.path * locals
    | Any of locals array

  type patterns = (EcIdent.t * pattern) list

  val create  : EcPath.path list list -> t
  val add     : patterns -> expr -> t -> unit
  val resolve : t -> opbranches
  exception PartialMatch of EcPath.path list list
  exception DuplicateMatch of patterns * patterns
  exception RedundantMatch  of patterns

  val pp_patterns : patterns -> TT.fix_match

end = struct

  type locals = (EcIdent.t * ty) list
  type pattern =
    | Single of int * EcPath.path * locals
    | Any of locals array

  type patterns = (EcIdent.t * pattern) list

  type t =
    | Case of (EcPath.path * t) array
    | Leaf of (patterns * locals list * expr) option ref

  exception PartialMatch of EcPath.path list list
  exception DuplicateMatch of patterns * patterns
  exception RedundantMatch  of patterns

  let rec create (inds : EcPath.path list list) =
    match inds with
    | [] -> Leaf (ref None)
    | ind :: inds ->
      let ind = Array.of_list ind in
      Case (Array.map (fun x -> (x, create inds)) ind)


  let add (current : patterns) e (m : t) =
    let filled = ref false in
    let rec add (weak : bool) rids bs (m : t) =
      match bs, m with
      | [], Leaf r ->
        begin match !r with
        | None -> r := Some (current, List.rev rids, e); filled := true
        | Some (previous, _, _) -> if not weak then raise (DuplicateMatch(previous, current))
        end
      | (_, Single (i, _, ids)) :: bs, Case t ->
          assert (i >= 0 && i < Array.length t);
          add weak (ids::rids) bs (snd t.(i))
      | (_, Any tids) :: bs, Case t ->
          assert (Array.length t = Array.length tids);
          for i = 0 to Array.length t - 1 do
            add true (tids.(i)::rids) bs (snd t.(i))
          done
      | _, _ -> assert false
    in
    add false [] current m;
    if not !filled then raise (RedundantMatch current)

  let check_partial m =
    let l = ref [] in
    let rec aux rps m =
      match m with
      | Case t ->
        Array.iter (fun (p,m) -> aux (p::rps) m) t
      | Leaf r ->
          if !r = None then l := List.rev rps :: !l
    in
    aux [] m;
    if !l <> [] then raise (PartialMatch !l)

  let resolve m =
    check_partial m;
    let rec resolve_r m =
      match m with
      | Case t ->
          let for1 i =
            let (cp, bs) =
              snd_map resolve_r t.(i)
            in
              { opb_ctor = (cp, i); opb_sub = bs; }
          in
            OPB_Branch (Parray.init (Array.length t) for1)

      | Leaf r -> begin
        match !r with
        | None -> assert false
        | Some (_, x1, x2) -> OPB_Leaf (x1, x2)
      end
  in
  resolve_r m

  let pp_pattern (x, p) =
    (x, match p with Any _ -> None | Single (_, p, _) -> Some p)

  let pp_patterns = List.map pp_pattern

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



let trans_matchfix
  ?(close = true) env ue { pl_loc = loc; pl_desc = name } (bd, pty, pbs)
=
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
          fxerror loc env TT.FXE_EmptyMatch

      | nm :: nms ->
          if not (List.for_all (Msym.set_equal nm) nms) then
            fxerror loc env TT.FXE_MatchParamsMixed;
          let argsmap =
            List.fold_lefti
              (fun m i (x, xty) -> Msym.add (EcIdent.name x) (i, x, xty) m)
              Msym.empty args
          in

          let _, mpty =
            Msym.fold_left
              (fun (seen, mpty) px _ ->
                 if Msym.mem px seen then
                   fxerror loc env TT.FXE_MatchParamsDup;

                 match Msym.find_opt px argsmap with
                 | None -> fxerror loc env TT.FXE_MatchParamsUnk
                 | Some (i, x, xty) -> (Ssym.add px seen, (i, x, xty) :: mpty))
              (Ssym.empty, []) nm
          in
            (mpty, pbsmap)
  in
  let mpty = List.rev mpty in
  (* First try to find the type of all matched inductive *)
  let add_ind indtbl ((_, x, _) : _ * EcIdent.t * _) =
    let x = EcIdent.name x in
    let rec add pbsmap =
      match pbsmap with
      | [] -> raise Not_found
      | (_, pbmap) :: pbsmap ->
        let pb = Msym.find x pbmap in
        match pb.pop_pattern with
        | PPAny -> add pbsmap
        | PPApp ((cname, tvi), _cargs) ->
            let tvi = tvi |> omap (TT.transtvi env ue) in
            let filter = fun _ op -> EcDecl.is_ctor op in
            let cts = EcUnify.select_op ~filter tvi env (unloc cname) ue ([], None) in
            match cts with
            | [] ->
              fxerror cname.pl_loc env TT.FXE_CtorUnk

            | _ :: _ :: _ ->
              fxerror cname.pl_loc env TT.FXE_CtorAmbiguous

            | [(cp, _tvi), _opty, _subue, _] ->
              let ctor = EcEnv.Op.by_path cp env in
              let (indp, _ctoridx) = EcDecl.operator_as_ctor ctor in
              let indty = EcEnv.Ty.by_path indp env in
              let ind = (oget (EcDecl.tydecl_as_datatype indty)).tydt_ctors in
              let ctors =
                List.map (fun (ctor, _) -> EcPath.pqoname (EcPath.prefix indp) ctor) ind in
              Msym.add x (indp, ctors) indtbl
    in
    add pbsmap in

  let indtbl = List.fold_left add_ind Msym.empty mpty in
  let inds =
      List.map (fun (_, x, _) -> snd (Msym.find (EcIdent.name x) indtbl)) mpty in
  let casemap = CaseMap.create inds in

  (* Build all branches and add them to the casemap *)
  let branches =
    let trans_b ((body, pbmap) : _ * pop_pattern Msym.t) =
      let trans1 ((_xpos, x0, xty) : _ * EcIdent.t * ty) =
        let x = EcIdent.name x0 in
        let pb = Msym.find x pbmap in
        match pb.pop_pattern with
        | PPAny ->
          let indp, _ = Msym.find x indtbl in
          let indty = oget (EcEnv.Ty.by_path_opt indp env) in
          let ind = (oget (EcDecl.tydecl_as_datatype indty)).tydt_ctors in
          let codom = tconstr indp (List.map tvar indty.tyd_params) in
          let tys = List.map (fun (_, dom) -> toarrow dom codom) ind in
          let tys, _ = EcUnify.UniEnv.opentys ue indty.tyd_params None tys in
          let doargs cty =
            let dom, codom = tyfun_flat cty in
            TT.unify_or_fail env ue pb.pop_name.pl_loc ~expct:codom xty;
            List.map (fun ty ->EcIdent.create "_", ty) dom in
          let args = List.map doargs tys in
          (x0, CaseMap.Any (Array.of_list args))
        | PPApp ((cname, tvi), cargs) ->
          let filter = fun _ op -> EcDecl.is_ctor op in
          let tvi = tvi |> omap (TT.transtvi env ue) in
          let cts = EcUnify.select_op ~filter tvi env (unloc cname) ue ([], None) in

          match cts with
          | [] ->
              fxerror cname.pl_loc env TT.FXE_CtorUnk

          | _ :: _ :: _ ->
              fxerror cname.pl_loc env TT.FXE_CtorAmbiguous

          | [(cp, tvi), opty, subue, _] ->
              let ctor = oget (EcEnv.Op.by_path_opt cp env) in
              let (indp, ctoridx) = EcDecl.operator_as_ctor ctor in
              let indty = oget (EcEnv.Ty.by_path_opt indp env) in
              let ind = (oget (EcDecl.tydecl_as_datatype indty)).tydt_ctors in
              let _ctorsym, ctorty = List.nth ind ctoridx in

              let args_exp = List.length ctorty in
              let args_got = List.length cargs in

              if args_exp <> args_got then
                fxerror cname.pl_loc env
                  (TT.FXE_CtorInvalidArity (snd (unloc cname), args_exp, args_got));

              let cargs_lin = List.pmap (fun o -> omap unloc (unloc o)) cargs in

              if not (List.is_unique cargs_lin) then
                fxerror cname.pl_loc env (TT.FXE_MatchNonLinear);

              EcUnify.UniEnv.restore ~src:subue ~dst:ue;

              let ctorty =
                let tvi = Some (EcUnify.TVIunamed tvi) in
                  fst (EcUnify.UniEnv.opentys ue indty.tyd_params tvi ctorty) in
              let pty = EcUnify.UniEnv.fresh ue in

              (try  EcUnify.unify env ue (toarrow ctorty pty) opty
               with EcUnify.UnificationFailure _ -> assert false);
              TT.unify_or_fail env ue pb.pop_name.pl_loc ~expct:pty xty;

              let create o =
                EcIdent.create (omap_dfl unloc "_" o) in
              let pvars = List.map (create -| unloc) cargs in
              let pvars = List.combine pvars ctorty in
              (x0, CaseMap.Single (ctoridx, cp, pvars))
      in

      let ptns = List.map trans1 mpty in
      let env  =
        List.fold_left (fun env (_, c) ->
          match c with
          | CaseMap.Any _ -> env
          | CaseMap.Single (_, _, pvars) -> EcEnv.Var.bind_locals pvars env)
          env ptns
      in

      let body = TT.transexpcast env `InOp ue codom body in

      try CaseMap.add ptns body casemap
      with
      | CaseMap.DuplicateMatch(previous, current) ->
          fxerror loc env
            (TT.FXE_FixDuplicate(CaseMap.pp_patterns previous, CaseMap.pp_patterns current))
      | CaseMap.RedundantMatch patterns ->
          fxerror loc env (TT.FXE_FixRedundant (CaseMap.pp_patterns patterns))
    in
    List.iter trans_b pbsmap;
    try CaseMap.resolve casemap
    with CaseMap.PartialMatch s -> fxerror loc env (TT.FXE_FixPartial s)
  in

  (* Check the guard condition *)
  let mf_recs = List.map proj3_1 mpty in
  let pos = List.max mf_recs in
  let n = oget (List.oindex ((=) pos) mf_recs) in
  let rec check_brs branches =
    match branches with
    | OPB_Branch t -> Parray.iter check_br t
    | OPB_Leaf (xss, e) ->
      let xs = List.nth xss n in
      let pvars = Sid.of_list (List.fst xs) in
      let rec check_body e =
        match destr_app e with
        | ({ e_node = Elocal x }, args) when x = opname -> begin
          match List.nth_opt args pos with
          | Some { e_node = Elocal a } when Sid.mem a pvars -> ()
          | _ -> fxerror loc env TT.FXE_SynCheckFailure
          end
        | _ -> EcTypes.e_iter check_body e
      in
      check_body e
  and check_br branch = check_brs branch.opb_sub
  in

  check_brs branches;

  (* Build the final result *)
  let aout =
    if close then
      let ts = Tuni.subst (EcUnify.UniEnv.assubst ue) in
      let tparams  = EcUnify.UniEnv.tparams ue in
      let codom    = ty_subst ts codom in
      let opexpr   = EcPath.pqname (EcEnv.root env) name in
      let args     = List.map (snd_map (ty_subst ts)) args in
      let opexpr   = e_op opexpr (List.map tvar tparams)
                       (toarrow (List.map snd args) codom) in
      let ebsubst  =
        bind_elocal ts opname opexpr
      in

      let branches =
        let rec uni_branches = function
          | OPB_Leaf (locals, e) ->
              OPB_Leaf (List.map (List.map (snd_map (ty_subst ts))) locals, e_subst ebsubst e)

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
           mf_recs     = mf_recs;
           mf_branches = branches; }

    else { mf_name     = opname;
           mf_codom    = codom;
           mf_args     = args;
           mf_recs     = mf_recs;
           mf_branches = branches; }
  in
  (ty, aout)
