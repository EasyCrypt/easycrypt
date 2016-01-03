(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2016 - Inria
 * 
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcSymbols
open EcIdent
open EcMaps
open EcUtils
open EcUid
open EcTypes
open EcDecl

module Sp = EcPath.Sp
module TC = EcTypeClass

(* -------------------------------------------------------------------- *)
exception UnificationFailure of [`TyUni of ty * ty | `TcCtt of ty * Sp.t]
exception UninstanciateUni

(* -------------------------------------------------------------------- *)
type pb = [ `TyUni of ty * ty | `TcCtt of ty * Sp.t ]

module UFArgs = struct
  module I = struct
    type t = uid

    let equal   = uid_equal
    let compare = uid_compare
  end

  module D = struct
    type data    = Sp.t * ty option
    type effects = pb list

    let default : data =
      (Sp.empty, None)

    let isvoid ((_, x) : data) =
      (x = None)

    let noeffects : effects = []

    let union d1 d2 =
      match d1, d2 with
      | (tc1, None), (tc2, None) ->
          ((Sp.union tc1 tc2, None), [])

      | (tc1, Some ty1), (tc2, Some ty2) ->
          ((Sp.union tc1 tc2, Some ty1), [`TyUni (ty1, ty2)])

      | (tc1, None   ), (tc2, Some ty)
      | (tc2, Some ty), (tc1, None   ) ->
          let tc = Sp.diff tc1 tc2 in
            if   Sp.is_empty tc
            then ((Sp.union tc1 tc2, Some ty), [])
            else ((Sp.union tc1 tc2, Some ty), [`TcCtt (ty, tc)])
  end
end

module UF = EcUFind.Make(UFArgs.I)(UFArgs.D)

(* -------------------------------------------------------------------- *)
module UnifyCore = struct
  let fresh ?(tc = Sp.empty) ?ty uf =
    let uid = EcUid.unique () in
    let uf  =
      match ty with
      | Some { ty_node = Tunivar id } ->
          let uf = UF.set uid (tc, None) uf in
            fst (UF.union uid id uf)
      | None | Some _ -> UF.set uid (tc, ty) uf
    in
      (uf, tuni uid)
end

(* -------------------------------------------------------------------- *)
let rec unify_core (env : EcEnv.env) (tvtc : Sp.t Mid.t) (uf : UF.t) pb =
  let failure () = raise (UnificationFailure pb) in

  let gr   = EcEnv.TypeClass.graph env in
  let inst = EcEnv.TypeClass.get_instances env in

  let uf = ref uf in
  let pb = let x = Queue.create () in Queue.push pb x; x in

  let instances_for_tcs tcs =
    let tcfilter (i, tc) =
      match tc with `General p -> Some (i, p) | _ -> None
    in
      List.filter
        (fun (_, tc1) ->
          Sp.for_all
            (fun tc2 -> TC.Graph.has_path ~src:tc1 ~dst:tc2 gr)
            tcs)
        (List.pmap tcfilter inst)
  in

  let has_tcs ~src ~dst =
    Sp.for_all
      (fun dst1 ->
        Sp.exists
          (fun src1 -> TC.Graph.has_path ~src:src1 ~dst:dst1 gr)
          src)
      dst
  in

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
    let (ti, effects) = UFArgs.D.union (UF.data i !uf) (Sp.empty, Some t) in
      if odfl false (snd ti |> omap (ocheck i)) then failure ();
      List.iter (Queue.push^~ pb) effects;
      uf := UF.set i ti !uf

  and getvar t =
    match t.ty_node with
    | Tunivar i -> snd_map (odfl t) (UF.data i !uf)
    | _ -> (Sp.empty, t)

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

            | Tglob mp, _ when EcEnv.NormMp.tglob_reducible env mp ->
                Queue.push (`TyUni (EcEnv.NormMp.norm_tglob env mp, t2)) pb

            | _, Tglob mp when EcEnv.NormMp.tglob_reducible env mp ->
                Queue.push (`TyUni (t1, EcEnv.NormMp.norm_tglob env mp)) pb

            | _, _ -> failure ()
        end
      end

      | `TcCtt (ty, tc) -> begin
          let tytc, ty = getvar ty in

          match ty.ty_node with
          | Tunivar i ->
              uf := UF.set i (Sp.union tc tytc, None) !uf

          | Tvar x ->
              let xtcs = odfl Sp.empty (Mid.find_opt x tvtc) in
                if not (has_tcs ~src:xtcs ~dst:tc) then
                  failure ()

          | _ ->
              if not (has_tcs ~src:tytc ~dst:tc) then
                let module E = struct exception Failure end in

                let inst = instances_for_tcs tc in

                let for1 uf p =
                   let for_inst ((typ, gty), p') =
                     try
                       if not (TC.Graph.has_path ~src:p' ~dst:p gr) then
                         raise E.Failure;
                       let (uf, gty) =
                         let (uf, subst) =
                           List.fold_left
                             (fun (uf, s) (v, tc) ->
                               let (uf, uid) = UnifyCore.fresh ~tc uf in
                                 (uf, Mid.add v uid s))
                             (uf, Mid.empty) typ
                         in
                           (uf, Tvar.subst subst gty)
                       in
                         try  Some (unify_core env tvtc uf (`TyUni (gty, ty)))
                         with UnificationFailure _ -> raise E.Failure
                     with E.Failure -> None
                   in
                     try  List.find_map for_inst inst
                     with Not_found -> failure ()
                in
                  uf := List.fold_left for1 !uf (Sp.elements tc)
      end
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

(* -------------------------------------------------------------------- *)
let subst_of_uf (uf : UF.t) =
  let close = close uf in
    fun id ->
      match close (tuni id) with
      | { ty_node = Tunivar id' } when uid_equal id id' -> None
      | t -> Some t

(* -------------------------------------------------------------------- *)
type unienv_r = {
  ue_uf     : UF.t;
  ue_named  : EcIdent.t Mstr.t;
  ue_tvtc   : Sp.t Mid.t;
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

  let create (vd : (EcIdent.t * Sp.t) list option) =
    let ue = {
      ue_uf     = UF.initial;
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

  let fresh ?tc ?ty ue =
    let (uf, uid) = UnifyCore.fresh ?tc ?ty (!ue).ue_uf in
      ue := { !ue with ue_uf = uf }; uid

  let opentvi ue (params : ty_params) tvi =
    match tvi with
    | None ->
        List.fold_left
          (fun s (v, tc) -> Mid.add v (fresh ~tc ue) s)
          Mid.empty params

    | Some (TVIunamed lt) ->
        List.fold_left2
          (fun s (v, tc) ty -> Mid.add v (fresh ~tc ~ty ue) s)
          Mid.empty params lt

    | Some (TVInamed lt) ->
        let for1 s (v, tc) =
          let t =
            try  fresh ~tc ~ty:(List.assoc (EcIdent.name v) lt) ue
            with Not_found -> fresh ~tc ue
          in
            Mid.add v t s
        in
          List.fold_left for1 Mid.empty params

  let subst_tv subst params =
    List.map (fun (tv, _) -> subst (tvar tv)) params

  let openty_r ue params tvi =
    let subst = Tvar.subst (opentvi ue params tvi) in
      (subst, subst_tv subst params)

  let opentys ue params tvi tys =
    let (subst, tvs) = openty_r ue params tvi in
      (List.map subst tys, tvs)

  let openty ue params tvi ty =
    let (subst, tvs) = openty_r ue params tvi in
      (subst ty, tvs)

  let rec repr (ue : unienv) (t : ty) : ty =
    match t.ty_node with
    | Tunivar id -> odfl t (snd (UF.data id (!ue).ue_uf))
    | _ -> t

  let closed (ue : unienv) =
    UF.closed (!ue).ue_uf

  let close (ue : unienv) =
    if not (closed ue) then raise UninstanciateUni;
    (subst_of_uf (!ue).ue_uf)

  let assubst ue = subst_of_uf (!ue).ue_uf

  let tparams ue =
    let fortv x = odfl Sp.empty (Mid.find_opt x (!ue).ue_tvtc) in
      List.map (fun x -> (x, fortv x)) (List.rev (!ue).ue_decl)
end

(* -------------------------------------------------------------------- *)
let unify env ue t1 t2 =
  let uf = unify_core env (!ue).ue_tvtc (!ue).ue_uf (`TyUni (t1, t2)) in
    ue := { !ue with ue_uf = uf; }

let hastc env ue ty tc =
  let uf = unify_core env (!ue).ue_tvtc (!ue).ue_uf (`TcCtt (ty, tc)) in
    ue := { !ue with ue_uf = uf; }

(* -------------------------------------------------------------------- *)
let tfun_expected ue psig =
  let tres = UniEnv.fresh ue in
    EcTypes.toarrow psig tres

(* -------------------------------------------------------------------- *)
type sbody = ((EcIdent.t * ty) list * expr) Lazy.t

(* -------------------------------------------------------------------- *)
let select_op ?(filter = fun _ -> true) tvi env name ue psig =
  let module D = EcDecl in

  let filter op =
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
      filter op && filter_on_tvi op
  in

  let select (path, op) =
    let module E = struct exception Failure end in

    let subue = UniEnv.copy ue in

    try
      begin try
        match tvi with
        | None ->
            ()

        | Some (TVIunamed lt) ->
            List.iter2
              (fun ty (_, tc) -> hastc env subue ty tc)
              lt op.D.op_tparams

        | Some (TVInamed ls) ->
            let tparams = List.map (fst_map EcIdent.name) op.D.op_tparams in
            let tparams = Msym.of_list tparams in
              List.iter (fun (x, ty) ->
                hastc env subue ty (oget (Msym.find_opt x tparams)))
                ls
        with UnificationFailure _ -> raise E.Failure
      end;

      let (tip, tvs) = UniEnv.openty_r subue op.D.op_tparams tvi in
      let top = tip op.D.op_ty in
      let texpected = tfun_expected subue psig in

      (try  unify env subue top texpected
       with UnificationFailure _ -> raise E.Failure);

      let bd =
        match op.D.op_kind with
        | OB_nott nt ->
           let substnt () =
             let xs = List.map (snd_map tip) nt.D.ont_args in
             let bd = EcTypes.e_mapty tip nt.D.ont_body in
             (xs, bd)
           in Some (Lazy.from_fun substnt)

        | _ -> None

      in Some ((path, tvs), top, subue, bd)

    with E.Failure -> None

  in
    List.pmap select (EcEnv.Op.all ~check:filter name env)
