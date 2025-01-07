(* -------------------------------------------------------------------- *)
open EcSymbols
open EcIdent
open EcMaps
open EcUtils
open EcAst
open EcTypes
open EcCoreSubst
open EcDecl

module Sp = EcPath.Sp

(* ==================================================================== *)
type problem = [
  | `TyUni of ty * ty
  | `TcTw  of tcwitness * tcwitness
  | `TcCtt of EcUid.uid * ty * typeclass
]

(* ==================================================================== *)
exception UnificationFailure of problem

exception UninstanciateUni

(* ==================================================================== *)
module Unify = struct
  module UFArgs = struct
    module I = struct
      type t = tyuni

      let equal   = TyUni.uid_equal
      let compare = TyUni.uid_compare
    end

    module D = struct
      type data    = ty option
      type effects = problem list

      let default : data =
        None

      let isvoid (x : data) =
        Option.is_none x

      let noeffects : effects = []

      let union (ty1 : data) (ty2 : data) : data * effects =
        let ty, cts =
          match ty1, ty2 with
          | None, None ->
              (None, [])
          | Some ty1, Some ty2 ->
              Some ty1, [(ty1, ty2)]

          | None, Some ty | Some ty, None ->
              Some ty, [] in

        let cts = List.map (fun x -> `TyUni x) cts in

        ty, (cts :> effects)
    end
  end

  (* ------------------------------------------------------------------ *)
  module UF = EcUFind.Make(UFArgs.I)(UFArgs.D)

  (* ------------------------------------------------------------------ *)
  type ucore = {
    uf    : UF.t;
    tvtc  : typeclass list Mid.t;
    tcenv : tcenv;
  }

  and tcenv = {
    (* Map from UID to TC problems. The UID set collects all the    *
     * unification variables the TC problem depends on. Only        *
     * fully instantiated problems trigger a type-class resolution. *
     * The UID is the univar from which the TC problem originates.  *)
    problems : (TyUni.Suid.t * typeclass list) TyUni.Muid.t;

    (* Map from univars to TC problems that depend on them. This    *
     * map is kept in sync with the UID set that appears in the     *
     * bindings of [problems]                                       *)
    byunivar : TyUni.Suid.t TyUni.Muid.t;

    (* Map from problems UID to type-class instance witness         *)
    resolution : tcwitness list TyUni.Muid.t
  }

  (* ------------------------------------------------------------------ *)
  let initial_ucore ?(tvtc = Mid.empty) () : ucore =
    let tcenv =
      { problems   = TyUni.Muid.empty
      ; byunivar   = TyUni.Muid.empty
      ; resolution = TyUni.Muid.empty }
    in { uf = UF.initial; tvtc; tcenv; }

  (* ------------------------------------------------------------------ *)
  let fresh
    ?(tcs : (typeclass * tcwitness option) list option)
    ?(ty : ty option)
    ({ uf; tcenv } as uc : ucore)
  =
    let uid = TyUni.unique () in

    let uf  =
      match ty with
      | Some { ty_node = Tunivar id } ->
          let uf = UF.set uid None uf in
          let ty, effects = UF.union uid id uf in
          assert (List.is_empty effects);
          ty
      | (None | Some _) as ty -> UF.set uid ty uf
    in

    let ty = Option.value ~default:(tuni uid) (UF.data uid uf) in

    let tcs, tws = List.split (Option.value ~default:[] tcs) in

    let tws = tws |> List.map (fun tcw ->
      match tcw with
      | None ->
        TCIUni (TcUni.unique ()) (* FIXME:TC *)
      | Some tcw ->
        tcw
    ) in

    let tcenv =
      let deps = Tuni.univars ty in
      let problems = TyUni.Muid.add uid (deps, tcs) tcenv.problems in
      let byunivar = TyUni.Suid.fold (fun duni byunivar ->
          TyUni.Muid.change (fun pbs ->
            Some (TyUni.Suid.add uid (Option.value ~default:TyUni.Suid.empty pbs))
          ) duni byunivar
        ) deps tcenv.byunivar in
      let resolution = TyUni.Muid.add uid tws tcenv.resolution in
      { problems; byunivar; resolution; }
    in

    ({ uc with uf; tcenv; }, (tuni uid, tws))

  (* ------------------------------------------------------------------ *)
  let unify_core (env : EcEnv.env) (uc : ucore) (pb : problem) : ucore =
    let failure () = raise (UnificationFailure pb) in

    let uf = ref uc.uf in
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
            | _ when Hint.mem map (i' :> int) -> false
            | _ ->
                match UF.data i' !uf with
                | None   -> Hint.add map (i' :> int) (); false
                | Some t ->
                  match doit t with
                  | true  -> true
                  | false -> Hint.add map (i' :> int) (); false
        end

        | _ -> EcTypes.ty_sub_exists doit t
      in
        doit t
    in

    let setvar i t =
      let (ti, effects) =
        UFArgs.D.union (UF.data i !uf) (Some t)
      in
        if odfl false (ti |> omap (ocheck i)) then failure ();
        List.iter (Queue.push^~ pb) effects;
        uf := UF.set i ti !uf

    and getvar t =
      match t.ty_node with
      | Tunivar i -> odfl t (UF.data i !uf)
      | _ -> t
    in

    let doit () =
      while not (Queue.is_empty pb) do
        match Queue.pop pb with
        | `TyUni (t1, t2) -> begin
          let (t1, t2) = (getvar t1, getvar t2) in

          match ty_equal t1 t2 with
          | true  -> ()
          | false -> begin
              match t1.ty_node, t2.ty_node with
              | Tunivar id1, Tunivar id2 -> begin
                  if not (TyUni.uid_equal id1 id2) then
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

                let ty1, tws1 = List.split lt1 in
                let ty2, tws2 = List.split lt2 in

                List.iter2 (fun t1 t2 -> Queue.push (`TyUni (t1, t2)) pb) ty1 ty2;

                List.iter2 (fun tw1 tw2 ->
                  if List.length tw1 <> List.length tw2 then failure ();
                  List.iter2 (fun w1 w2 -> Queue.push (`TcTw (w1, w2)) pb) tw1 tw2
                ) tws1 tws2

              | Tconstr (p, lt), _ when EcEnv.Ty.defined p env ->
                  Queue.push (`TyUni (EcEnv.Ty.unfold p lt env, t2)) pb

              | _, Tconstr (p, lt) when EcEnv.Ty.defined p env ->
                  Queue.push (`TyUni (t1, EcEnv.Ty.unfold p lt env)) pb

              | _, _ -> failure ()
          end
        end

        | _ ->
          () (* FIXME:TC *)
      done
    in
      doit (); { uc with uf = !uf }

  (* -------------------------------------------------------------------- *)
  let close (uc : ucore) =
    let map = Hint.create 0 in

    let rec doit t =
      match t.ty_node with
      | Tunivar i -> begin
          match Hint.find_opt map (i :> int) with
          | Some t -> t
          | None   -> begin
            let t =
              match UF.data i uc.uf with
              | None   -> tuni (UF.find i uc.uf)
              | Some t -> doit t
            in
              Hint.add map (i :> int) t; t
          end
      end

      | _ -> ty_map doit t
    in
      fun t -> doit t

  (* ------------------------------------------------------------------ *)
  let subst_of_uf (uc : ucore) =
    let close = close uc in
    List.fold_left (fun m uid ->
      match close (tuni uid) with
      | { ty_node = Tunivar uid' } when TyUni.uid_equal uid uid' -> m
      | t -> TyUni.Muid.add uid t m
    ) TyUni.Muid.empty (UF.domain uc.uf)
end

(* -------------------------------------------------------------------- *)
type unienv_r = {
  ue_uc     : Unify.ucore;
  ue_named  : EcIdent.t Mstr.t;
  ue_decl   : EcIdent.t list;
  ue_closed : bool;
}

type unienv = unienv_r ref

type petyarg = ty option * tcwitness option list option

type tvar_inst =
| TVIunamed of petyarg list
| TVInamed  of (EcSymbols.symbol * petyarg) list

type tvi = tvar_inst option

let tvi_unamed (ety : etyarg list) : tvar_inst =
  TVIunamed (List.map
    (fun (ty, tcw) -> Some ty, Some (List.map Option.some tcw))
    ety
  )

module UniEnv = struct
  let copy (ue : unienv) : unienv =
    ref !ue

  let restore ~(dst:unienv) ~(src:unienv) =
    dst := !src

  let getnamed (ue : unienv) (x : symbol) =
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

  let create (vd : (EcIdent.t * typeclass list) list option) : unienv =
    let ue =
      match vd with
      | None ->
        { ue_uc     = Unify.initial_ucore ()
        ; ue_named  = Mstr.empty
        ; ue_decl   = []
        ; ue_closed = false
        }

      | Some vd ->
          let vdmap = List.map (fun (x, _) -> (EcIdent.name x, x)) vd in
          let tvtc  = Mid.of_list vd in
          { ue_uc = Unify.initial_ucore ~tvtc ()
          ; ue_named  = Mstr.of_list vdmap
          ; ue_decl   = List.rev_map fst vd
          ; ue_closed = true;
          }
      in ref ue

  let xfresh
    ?(tcs : (typeclass * tcwitness option) list option)
    ?(ty : ty option)
    (ue : unienv)
  =
    let (uc, tytw) = Unify.fresh ?tcs ?ty (!ue).ue_uc in
    ue := { !ue with ue_uc = uc }; tytw

  let fresh ?(ty : ty option) (ue : unienv) =
    let (uc, (ty, tw)) = Unify.fresh ?ty (!ue).ue_uc in
    assert (List.is_empty tw);
    ue := { !ue with ue_uc = uc }; ty

  type opened = {
    subst  : etyarg Mid.t;
    params : (ty * typeclass list) list;
    args   : etyarg list;
  }  

  let subst_tv (subst : etyarg Mid.t) (params : ty_params) =
    List.map (fun (tv, tcs) ->
      let tv = Tvar.subst subst (tvar tv) in
      let tcs =
        List.map
          (fun tc ->
            let tc_args =
              List.map (Tvar.subst_etyarg subst) tc.tc_args 
            in { tc with tc_args })
          tcs
      in (tv, tcs)) params

  let opentvi (ue : unienv) (params : ty_params) (tvi : tvi) : opened =
    let tvi =
      match tvi with
      | None ->
          List.map (fun (v, tcs) ->
            (v, (None, List.map (fun x -> (x, None)) tcs))
          ) params

      | Some (TVIunamed lt) ->
          let combine (v, tc) (ty, tcw) =
            let tctcw =
              match tcw with
              | None ->
                List.map (fun tc -> (tc, None)) tc
              | Some tcw ->
                List.combine tc tcw
            in (v, (ty, tctcw)) in

          List.map2 combine params lt

      | Some (TVInamed lt) ->
          List.map (fun (v, tc) ->
            let ty, tcw =
                 List.assoc_opt (EcIdent.name v) lt
              |> Option.value ~default:(None, None) in

            let tcw =
              match tcw with
              | None ->
                List.map (fun _ -> None) tc
              | Some tcw ->
                tcw in
            
            (v, (ty, List.map2 (fun x y -> (x, y)) tc tcw))
          ) params
    in

    let subst =
      List.fold_left (fun s (v, (ty, tcws)) ->
        let tcs =
          let for1 (tc, tcw) =
            let tc =
              { tc_name = tc.tc_name;
                tc_args = List.map (Tvar.subst_etyarg s) tc.tc_args } in
            (tc, tcw)
          in List.map for1 tcws
        in Mid.add v (xfresh ?ty ~tcs ue) s
      ) Mid.empty tvi in

    let args = List.map (fun (x, _) -> oget (Mid.find_opt x subst)) params in
    let params = subst_tv subst params in

    { subst; args; params; }

  let opentys (ue : unienv) (params : ty_params) (tvi : tvi) (tys : ty list) =
    let opened = opentvi ue params tvi in
    let tys = List.map (Tvar.subst opened.subst) tys in
    tys, opened

  let openty (ue : unienv) (params : ty_params) (tvi : tvi) (ty : ty) =
    let opened = opentvi ue params tvi in
    Tvar.subst opened.subst ty, opened

  let repr (ue : unienv) (t : ty) : ty =
    match t.ty_node with
    | Tunivar id -> odfl t (Unify.UF.data id (!ue).ue_uc.uf)
    | _ -> t

  let closed (ue : unienv) =
    Unify.UF.closed (!ue).ue_uc.uf (* FIXME:TC *)

  let assubst (ue : unienv) =
    { uvars = Unify.subst_of_uf (!ue).ue_uc
    ; utcvars = TcUni.Muid.empty; (* FIXME:TC *) }

  let close (ue : unienv) =
    if not (closed ue) then raise UninstanciateUni;
    assubst ue

  let tparams (ue : unienv) =
    let fortv x = odfl [] (Mid.find_opt x (!ue).ue_uc.tvtc) in
      List.map (fun x -> (x, fortv x)) (List.rev (!ue).ue_decl)
end

(* -------------------------------------------------------------------- *)
let unify_core (env : EcEnv.env) (ue : unienv) (pb : problem) =
  let uc = Unify.unify_core env (!ue).ue_uc pb in
  ue := { !ue with ue_uc = uc; }

(* -------------------------------------------------------------------- *)
let unify (env : EcEnv.env) (ue : unienv) (t1 : ty) (t2 : ty) =
  unify_core env ue (`TyUni (t1, t2))

(* -------------------------------------------------------------------- *)
let tfun_expected (ue : unienv) (psig : ty list) =
  EcTypes.toarrow psig (UniEnv.fresh ue)

(* -------------------------------------------------------------------- *)
type sbody = ((EcIdent.t * ty) list * expr) Lazy.t

(* -------------------------------------------------------------------- *)
type select_filter_t = EcPath.path -> operator -> bool

type select_t =
  ((EcPath.path * etyarg list) * ty * unienv * sbody option) list

let select_op
  ?(hidden : bool = false)
  ?(filter : select_filter_t = fun _ _ -> true)
   (tvi    : tvi) 
   (env    : EcEnv.env)
   (name   : qsymbol)
   (ue     : unienv)
   (psig   : dom)
  : select_t
=
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
      let UniEnv.{ subst = tip; args } =
        UniEnv.opentvi subue op.D.op_tparams tvi in
      let tip = f_subst_init ~tv:tip () in

      (*
      List.iter
        (fun (tv, tcs) ->
          try  hastcs_r env subue tv tcs
          with UnificationFailure _ -> raise E.Failure)
        tvtcs;
      *)

      let top = EcCoreSubst.ty_subst tip op.D.op_ty in
      let texpected = tfun_expected subue psig in

      (try  unify env subue top texpected
       with UnificationFailure _ -> raise E.Failure);

      let bd =
        match op.D.op_kind with
        | OB_nott nt ->
           let substnt () =
             let xs = List.map (snd_map (ty_subst tip)) nt.D.ont_args in
             let es = e_subst tip in
             let bd = es nt.D.ont_body in
             (xs, bd)
           in Some (Lazy.from_fun substnt)

        | _ -> None
      in

      Some ((path, args), top, subue, bd) (* FIXME:TC *)

    with E.Failure -> None

  in
    List.pmap select (EcEnv.Op.all ~check:filter ~name env)
