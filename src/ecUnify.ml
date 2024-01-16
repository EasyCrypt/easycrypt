(* -------------------------------------------------------------------- *)
open EcSymbols
open EcIdent
open EcMaps
open EcUtils
open EcUid
open EcAst
open EcTypes
open EcDecl

module Sp = EcPath.Sp

(* -------------------------------------------------------------------- *)
exception UnificationFailure of [`TyUni of ty * ty | `TcCtt of ty * typeclass]
exception UninstanciateUni

(* ==================================================================== *)
module type UFRaw = sig
  type uf
  type data

  val set : uid -> data * ty option -> uf -> uf
end

(* ==================================================================== *)
module type UnifyExtra = sig
  type state
  type problem

  exception Failure

  module State : sig
    val default : state
    val union   : state * ty option -> state * ty option -> state * problem list
  end

  module Problem : sig
    val solve :
      (module EcUFind.S
        with type t    = 'uf
         and type item = uid
         and type data = state * ty option)
      -> 'uf ref -> EcEnv.env -> state Mid.t -> problem -> problem list
  end
end

(* ==================================================================== *)
module UnifyGen(X : UnifyExtra) = struct
  (* ------------------------------------------------------------------ *)
  type pb = [ `TyUni of (ty * ty) | `Other of X.problem ]

  exception UnificationFailure of pb

  module UFArgs = struct
    module I = struct
      type t = uid

      let equal   = uid_equal
      let compare = uid_compare
    end

    module D = struct
      type data    = X.state * ty option
      type effects = pb list

      let default : data =
        (X.State.default, None)

      let isvoid ((_, x) : data) =
        (x = None)

      let noeffects : effects = []

      let union ((_, ty1) as d1 : data) ((_, ty2) as d2 : data) : data * effects =
        let pb, cts_pb = X.State.union d1 d2 in
        let ty, cts_ty =
          match ty1, ty2 with
          | None, None ->
              (None, [])
          | Some ty1, Some ty2 ->
              Some ty1, [(ty1, ty2)]

          | None, Some ty | Some ty, None ->
              Some ty, [] in

        let cts =
            (List.map (fun x -> `Other x) cts_pb)
          @ (List.map (fun x -> `TyUni x) cts_ty) in

        (pb, ty), (cts :> effects)
    end
  end

  (* ------------------------------------------------------------------ *)
  module UF = EcUFind.Make(UFArgs.I)(UFArgs.D)

  (* ------------------------------------------------------------------ *)
  let fresh ?(extra = X.State.default) ?ty uf =
    let uid = EcUid.unique () in
    let uf  =
      match ty with
      | Some { ty_node = Tunivar id } ->
          let uf = UF.set uid (extra, None) uf in
          fst (UF.union uid id uf)
      | None | Some _ -> UF.set uid (extra, ty) uf
    in
      (uf, tuni uid)

  (* ------------------------------------------------------------------ *)
  let unify_core (env : EcEnv.env) (tvtc : X.state Mid.t) (uf : UF.t) pb =
    let failure () = raise (UnificationFailure pb) in

    let uf = ref uf in
    let pb = let x = Queue.create () in Queue.push pb x; x in

    let ocheck i t =
      let i   = UF.find i !uf in
      let map = Hint.create 0 in

      let rec doit t =
        match t.ty_node with
        | Tunivar i' -> begin
            let i' = UF.find i' !uf in
              match i' with
              | _ when i = i' -> true
              | _ when Hint.mem map i' -> false
              | _ ->
                  match snd (UF.data i' !uf) with
                  | None   -> Hint.add map i' (); false
                  | Some t ->
                    match doit t with
                    | true  -> true
                    | false -> Hint.add map i' (); false
        end

        | _ -> EcTypes.ty_sub_exists doit t
      in
        doit t
    in

    let setvar i t =
      let (ti, effects) =
        UFArgs.D.union (UF.data i !uf) (X.State.default, Some t)
      in
        if odfl false (snd ti |> omap (ocheck i)) then failure ();
        List.iter (Queue.push^~ pb) effects;
        uf := UF.set i ti !uf

    and getvar t =
      match t.ty_node with
      | Tunivar i -> snd_map (odfl t) (UF.data i !uf)
      | _ -> (X.State.default, t)

    in

    let doit () =
      while not (Queue.is_empty pb) do
        match Queue.pop pb with
        | `TyUni (t1, t2) -> begin
          let (t1, t2) = (snd (getvar t1), snd (getvar t2)) in

          match ty_equal t1 t2 with
          | true  -> ()
          | false -> begin
              match t1.ty_node, t2.ty_node with
              | Tunivar id1, Tunivar id2 -> begin
                  if not (uid_equal id1 id2) then
                    let effects = reffold (swap |- UF.union id1 id2) uf in
                    List.iter (Queue.push^~ pb) effects
              end

              | Tunivar id, _ -> setvar id t2
              | _, Tunivar id -> setvar id t1

              | Ttuple lt1, Ttuple lt2 ->
                  if List.length lt1 <> List.length lt2 then failure ();
                  List.iter2 (fun t1 t2 -> Queue.push (`TyUni (t1, t2)) pb) lt1 lt2

              | Tfun (t1, t2), Tfun (t1', t2') ->
                  Queue.push (`TyUni (t1, t1')) pb;
                  Queue.push (`TyUni (t2, t2')) pb

              | Tconstr (p1, lt1), Tconstr (p2, lt2) when EcPath.p_equal p1 p2 ->
                  if List.length lt1 <> List.length lt2 then failure ();
                  List.iter2 (fun t1 t2 -> Queue.push (`TyUni (t1, t2)) pb) lt1 lt2

              | Tconstr (p, lt), _ when EcEnv.Ty.defined p env ->
                  Queue.push (`TyUni (EcEnv.Ty.unfold p lt env, t2)) pb

              | _, Tconstr (p, lt) when EcEnv.Ty.defined p env ->
                  Queue.push (`TyUni (t1, EcEnv.Ty.unfold p lt env)) pb

              | _, _ -> failure ()
          end
        end

        | `Other pb1 ->
            try
              List.iter
                (fun x -> Queue.push (`Other x) pb)
                (X.Problem.solve (module UF) uf env tvtc pb1)
            with X.Failure -> failure ()
      done
    in
      doit (); !uf

  (* -------------------------------------------------------------------- *)
  let close (uf : UF.t) =
    let map = Hint.create 0 in

    let rec doit t =
      match t.ty_node with
      | Tunivar i -> begin
         match Hint.find_opt map i with
         | Some t -> t
         | None   -> begin
           let t =
             match snd (UF.data i uf) with
             | None   -> tuni (UF.find i uf)
             | Some t -> doit t
           in
             Hint.add map i t; t
         end
      end

      | _ -> ty_map doit t
    in
      fun t -> doit t

  (* ------------------------------------------------------------------ *)
  let subst_of_uf (uf : UF.t) =
    let close = close uf in
    List.fold_left (fun m uid ->
      match close (tuni uid) with
      | { ty_node = Tunivar uid' } when uid_equal uid uid' -> m
      | t -> Muid.add uid t m
    )
    Muid.empty (UF.domain uf)
end

(* -------------------------------------------------------------------- *)
module UnifyExtraEmpty :
  UnifyExtra with type state   = unit
              and type problem = unit =
struct
  type state   = unit
  type problem = unit
  type uparam  = state * ty option

  exception Failure

  module State = struct
    let default : state =
      ()

    let union (_ : uparam) (_ : uparam) : state * problem list =
      ((), [])
  end

  module Problem = struct
    let solve (type uf) (module _)
      (_ : uf ref) (_ : EcEnv.env) (_ : state Mid.t) (() : problem)
    =
      []
  end
end

(* -------------------------------------------------------------------- *)
module UnifyCore = UnifyGen(UnifyExtraEmpty)

(* -------------------------------------------------------------------- *)
module TypeClass = struct
  let hastc
        (env : EcEnv.env) (tvtc : (typeclass list) Mid.t)
        (ty : ty) (tc : typeclass)
    =

    let instances = EcEnv.TypeClass.get_instances env in

    let instances =
      List.filter_map
        (function (x, `General (y, syms)) -> Some (x, y, syms) | _ -> None)
        instances in

    let instances =
      (* FIXME:TC *)
      let ring  = EcPath.fromqsymbol ([EcCoreLib.i_top], "Ring" ) in
      let field = EcPath.fromqsymbol ([EcCoreLib.i_top], "Field") in

      List.filter
        (fun (_, tc, _) ->
          List.for_all
            (fun p -> not (EcPath.isprefix p tc.tc_name))
            [ring; field])
        instances in

    let instances =
      let tvinst =
        List.map
          (fun (tv, tcs) ->
             List.map (fun tc -> (([], tvar tv), tc, None)) tcs)
          (Mid.bindings tvtc)
      in List.flatten tvinst @ instances in

    let exception Bailout in

    let rec find_tc_in_parent acc tginst =
      if EcPath.p_equal tc.tc_name tginst.tc_name then
        Some (tginst.tc_args, List.rev acc)
      else
        let tcdecl = EcEnv.TypeClass.by_path tginst.tc_name env in
        tcdecl.tc_prt |> obind (fun prt ->
          let acc = (tcdecl.tc_tparams, tginst.tc_args) :: acc in
          find_tc_in_parent acc prt) in

    let for1 ((tgparams, tgty), tginst, (opsyms : (EcPath.path * ty list) Mstr.t option)) =
      let tgi_args, tgparams_prt  =
        oget ~exn:Bailout (find_tc_in_parent [] tginst) in

      let uf, tvinfo =
        List.fold_left_map
          (fun uf (tv, tcs) ->
            let uf, tvty = UnifyCore.fresh uf in uf, (tv, (tvty, tcs)))
          UnifyCore.UF.initial tgparams in

      let subst =
        Mid.of_list (List.map (snd_map fst) tvinfo) in

      let subst as subst0 =
        let tcsubst =
          List.fold_left
            (fun subst (tparams, args) ->
               let args  = List.map (Tvar.subst subst) args in
               let subst = List.combine (List.fst tparams) args in
               Mid.of_list subst)
            subst tgparams_prt in

        Mid.fold
          (fun x ty subst -> Mid.add x ty subst)
          tcsubst subst in

      let uf, tgi_args = ref uf, List.map (Tvar.subst subst) tgi_args in

      List.iter2
        (fun pty tgty ->
           let tgty = Tvar.subst subst tgty in
           try
             uf := UnifyCore.unify_core env Mid.empty !uf (`TyUni (pty, tgty))
           with UnifyCore.UnificationFailure _ ->
             raise Bailout)
        tc.tc_args tgi_args;

      let tgty = Tvar.subst subst tgty in

      begin try
        uf := UnifyCore.unify_core env Mid.empty !uf (`TyUni (ty, tgty))
      with UnifyCore.UnificationFailure _ -> raise Bailout end;

      let subst = UnifyCore.subst_of_uf !uf in
      let subst = ty_subst (Tuni.subst subst) in

      (* assert (UnifyCore.UF.closed !uf); *)

      let opsyms = opsyms |> Option.map (
          Mstr.map
            (fun (p, tys) ->
              (p, List.map (fun ty -> subst (Tvar.subst subst0 ty)) tys))
        ) in

      let effects =
        List.flatten (List.map
          (fun (_, (ty, tcs)) ->
            List.map (fun tc -> (subst ty, tc)) tcs)
          tvinfo)

      in (effects, opsyms)

    in

    let for1 pb =
      try Some (for1 pb) with Bailout -> None in

    List.find_map_opt for1 instances
end

(* -------------------------------------------------------------------- *)
type tcproblem = [
  `TcCtt of ty * typeclass * ((EcPath.path * ty list) Mstr.t) option ref
]

module UnifyExtraForTC :
  UnifyExtra with type state   = typeclass list
              and type problem = tcproblem =
struct
  type state   = typeclass list
  type problem = tcproblem
  type uparam  = state * ty option

  exception Failure

  module State = struct
    let default : state =
      []

    let union (d1 : uparam) (d2 : uparam) =
      match d1, d2 with
      | (tc1, None), (tc2, None) ->
          (tc1 @ tc2), []

      | (tc1, Some _), (tc2, Some _) ->
          (tc1 @ tc2), []

      | (tc1, None   ), (tc2, Some ty)
      | (tc2, Some ty), (tc1, None   ) ->
          (tc1 @ tc2), List.map (fun tc -> `TcCtt (ty, tc, ref None)) tc1
  end

  module Problem = struct
    let solve (type uf)
      (module UF : EcUFind.S
              with type t    = uf
               and type item = uid
               and type data = uparam)
      (uf   : uf ref)
      (env  : EcEnv.env)
      (tvtc : state Mid.t)
      (pb   : problem)
      : problem list
    =
      let `TcCtt (ty, tc, tcrec) = pb in

      let tytc, ty =
        match ty.ty_node with
        | Tunivar i -> snd_map (odfl ty) (UF.data i !uf)
        | _ -> (State.default, ty) in

        match ty.ty_node with
        | Tunivar i ->
            uf := UF.set i (tc :: tytc, None) !uf;
            []

        | _ -> begin
            match TypeClass.hastc env tvtc ty tc with
            | None ->
                raise Failure
            | Some (effects, opsyms) ->
                tcrec := opsyms;
                List.map (fun (ty, tc) -> `TcCtt (ty, tc, ref None)) effects
        end
  end
end

(* -------------------------------------------------------------------- *)
module Unify = UnifyGen(UnifyExtraForTC)

(* -------------------------------------------------------------------- *)
type unienv_r = {
  ue_uf     : Unify.UF.t;
  ue_named  : EcIdent.t Mstr.t;
  ue_tvtc   : typeclass list Mid.t;
  ue_decl   : EcIdent.t list;
  ue_closed : bool;
}

type unienv = unienv_r ref

type tvar_inst =
| TVIunamed of ty list
| TVInamed  of (EcSymbols.symbol * ty) list

type tvi = tvar_inst option
type uidmap = uid -> ty option

module UniEnv = struct
  let copy (ue : unienv) : unienv =
    ref !ue

  let restore ~(dst:unienv) ~(src:unienv) =
    dst := !src

  let getnamed ue x =
      match Mstr.find_opt x (!ue).ue_named with
      | Some a -> a
      | None   -> begin
          if (!ue).ue_closed then raise Not_found;
          let id = EcIdent.create x in
            ue := { !ue with
              ue_named = Mstr.add x id (!ue).ue_named;
              ue_decl  = id :: (!ue).ue_decl;
            }; id
    end

  let create (vd : (EcIdent.t * typeclass list) list option) =
    let ue = {
      ue_uf     = Unify.UF.initial;
      ue_named  = Mstr.empty;
      ue_tvtc   = Mid.empty;
      ue_decl   = [];
      ue_closed = false;
    } in

    let ue =
      match vd with
      | None    -> ue
      | Some vd ->
          let vdmap = List.map (fun (x, _) -> (EcIdent.name x, x)) vd in
            { ue with
                ue_named  = Mstr.of_list vdmap;
                ue_tvtc   = Mid.of_list vd;
                ue_decl   = List.rev_map fst vd;
                ue_closed = true; }
    in
      ref ue

  let fresh ?tcs ?ty ue =
    let (uf, uid) = Unify.fresh ?extra:tcs ?ty (!ue).ue_uf in
      ue := { !ue with ue_uf = uf }; uid

  let opentvi ue (params : ty_params) tvi =
    let tvi =
      match tvi with
      | None ->
          List.map (fun (v, tc) -> (v, (None, tc))) params

      | Some (TVIunamed lt) ->
          List.map2 (fun (v, tc) ty -> (v, (Some ty, tc))) params lt

      | Some (TVInamed lt) ->
          List.map (fun (v, tc) ->
            let ty = List.assoc_opt (EcIdent.name v) lt in
            (v, (ty, tc))
          ) params in

    List.fold_left (fun s (v, (ty, tcs)) ->
        let tcs =
          let for1 tc =
            { tc_name = tc.tc_name;
              tc_args = List.map (Tvar.subst s) tc.tc_args } in
          List.map for1 tcs in
        Mid.add v (fresh ?ty:ty ~tcs ue) s
      ) Mid.empty tvi

  let subst_tv subst params =
    List.map (fun (tv, tcs) ->
      let tv = subst (tvar tv) in
      let tcs =
        List.map
          (fun tc -> { tc with tc_args = List.map subst tc.tc_args })
          tcs
      in (tv, tcs)) params

  let openty_r ue params tvi =
    let subst = { ty_subst_id with ts_v = (opentvi ue params tvi) } in
    (subst, subst_tv (ty_subst subst) params)

  let opentys ue params tvi tys =
    let (subst, tvs) = openty_r ue params tvi in
    (List.map (ty_subst subst) tys, tvs)

  let openty ue params tvi ty =
    let (subst, tvs) = openty_r ue params tvi in
    (ty_subst subst ty, tvs)

  let repr (ue : unienv) (t : ty) : ty =
    match t.ty_node with
    | Tunivar id -> odfl t (snd (Unify.UF.data id (!ue).ue_uf))
    | _ -> t

  let closed (ue : unienv) =
    Unify.UF.closed (!ue).ue_uf

  let close (ue : unienv) =
    if not (closed ue) then raise UninstanciateUni;
    (Unify.subst_of_uf (!ue).ue_uf)

  let assubst ue = Unify.subst_of_uf (!ue).ue_uf

  let tparams ue =
    let fortv x = odfl [] (Mid.find_opt x (!ue).ue_tvtc) in
      List.map (fun x -> (x, fortv x)) (List.rev (!ue).ue_decl)
end

(* -------------------------------------------------------------------- *)
let unify_core env ue pb =
  let uf =
    try
      Unify.unify_core env (!ue).ue_tvtc (!ue).ue_uf pb
    with Unify.UnificationFailure pb -> begin
      match pb with
      | `TyUni (ty1, ty2) ->
          raise (UnificationFailure (`TyUni (ty1, ty2)))
      | `Other (`TcCtt (ty, tc, _)) ->
          raise (UnificationFailure (`TcCtt (ty, tc)))
      end
  in ue := { !ue with ue_uf = uf; }

(* -------------------------------------------------------------------- *)
let unify env ue t1 t2 =
  unify_core env ue (`TyUni (t1, t2))

let xhastc_r env ue ty tc =
  let instance = ref None in
  unify_core env ue (`Other (`TcCtt (ty, tc, instance)));
  !instance

let hastc_r env ue ty tc =
  ignore (xhastc_r env ue ty tc : _ option)

let xhastcs_r env ue ty tcs =
  List.map (hastc_r env ue ty) tcs

let hastcs_r env ue ty tcs =
  List.iter (hastc_r env ue ty) tcs

(* -------------------------------------------------------------------- *)
let hastc env ue ty tc =
  try  Some (xhastc_r env ue ty tc)
  with UnificationFailure _ -> None

(* -------------------------------------------------------------------- *)
let tfun_expected ue psig =
  let tres = UniEnv.fresh ue in
    EcTypes.toarrow psig tres

(* -------------------------------------------------------------------- *)
type sbody = ((EcIdent.t * ty) list * expr) Lazy.t

(* -------------------------------------------------------------------- *)
let select_op ?(hidden = false) ?(filter = fun _ _ -> true) tvi env name ue psig =
  ignore hidden;                (* FIXME *)

  let module D = EcDecl in

  let filter oppath op =
    (* Filter operator based on given type variables instanciation *)
    let filter_on_tvi =
      match tvi with
      | None -> fun _ -> true

      | Some (TVIunamed lt) ->
          let len = List.length lt in
            fun op ->
              let tparams = op.D.op_tparams in
              List.length tparams = len

      | Some (TVInamed ls) -> fun op ->
          let tparams = List.map (fst_map EcIdent.name) op.D.op_tparams in
          let tparams = Msym.of_list tparams in
          List.for_all (fun (x, _) -> Msym.mem x tparams) ls

    in
      filter oppath op && filter_on_tvi op
  in

  let select (path, op) =
    let module E = struct exception Failure end in

    let subue = UniEnv.copy ue in

    try
      let (tip, tvtcs) = UniEnv.openty_r subue op.D.op_tparams tvi in

      List.iter
        (fun (tv, tcs) ->
          try  hastcs_r env subue tv tcs
          with UnificationFailure _ -> raise E.Failure)
        tvtcs;

      let top = ty_subst tip op.D.op_ty in
      let texpected = tfun_expected subue psig in

      (try  unify env subue top texpected
       with UnificationFailure _ -> raise E.Failure);

      let bd =
        match op.D.op_kind with
        | OB_nott nt ->
           let substnt () =
             let xs = List.map (snd_map (ty_subst tip)) nt.D.ont_args in
             let es = e_subst { e_subst_id with es_ty = tip } in
             let bd = es nt.D.ont_body in
             (xs, bd)
           in Some (Lazy.from_fun substnt)

        | _ -> None

      in Some ((path, List.fst tvtcs), top, subue, bd)

    with E.Failure -> None

  in
    List.pmap select (EcEnv.Op.all ~check:filter ~name env)
