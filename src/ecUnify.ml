(* -------------------------------------------------------------------- *)
open EcMaps
open EcUtils
open EcUidgen
open EcSymbols
open EcIdent
open EcTypes
open EcDecl

module Sp = EcPath.Sp
module TC = EcTypeClass

(* -------------------------------------------------------------------- *)
exception UnificationFailure of ty * ty
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
          let tc = Sp.diff tc2 tc1 in
            if   Sp.is_empty tc
            then ((Sp.union tc1 tc2, Some ty), [])
            else ((Sp.union tc1 tc2, Some ty), [`TcCtt (ty, tc)])

  end
end

module UF = EcUFind.Make(UFArgs.I)(UFArgs.D)

(* -------------------------------------------------------------------- *)
type tvtc = TC.nodes

let hastc env tvtc ty tc =
  let tytc =
    match ty.ty_node with
    | Tvar    x      -> odfl Sp.empty (Mid.find_opt x tvtc)
    | Tconstr (p, _) -> EcEnv.TypeClass.tc_of_typename p env
    | _              -> Sp.empty

  and gr = EcEnv.TypeClass.graph env in

    Sp.for_all
      (fun dst ->
        let check = fun src -> TC.Graph.has_path ~src ~dst gr in
          Sp.exists check tytc)
      tc

let unify_core (env : EcEnv.env) (tvtc : Sp.t Mid.t) (uf : UF.t) t1 t2 =
  let failure () = raise (UnificationFailure (t1, t2)) in

  let uf = ref uf in
  let pb = let x = Queue.create () in Queue.push (`TyUni (t1, t2)) x; x in

  let ocheck i t =
    let map = Hint.create 0 in

    let rec doit t =
      match t.ty_node with
      | Tunivar i' when uid_equal i i'  -> true
      | Tunivar i' when Hint.mem map i' -> false
      | Tunivar i' -> begin
          match snd (UF.data i' !uf) with
          | None   -> Hint.add map i' (); false
          | Some t -> begin
            match doit t with
            | true  -> true
            | false -> Hint.add map i' (); false
          end
      end

      | _ -> EcTypes.ty_sub_exists doit t
    in
      doit t
  in

  let setvar i t =
    if ocheck i t then failure ();
    let (ti, effects) = UFArgs.D.union (UF.data i !uf) (Sp.empty, Some t) in
      List.iter (Queue.push^~ pb) effects;
      uf := UF.set i ti !uf
  in

  let doit () =
    while not (Queue.is_empty pb) do
      match Queue.pop pb with
      | `TyUni (t1, t2) -> begin
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
      
            | Tglob mp1, Tglob mp2 ->
                let mp1 = EcEnv.NormMp.norm_tglob env mp1 in
                let mp2 = EcEnv.NormMp.norm_tglob env mp2 in
                  if not (ty_equal mp1 mp2) then failure ()

            | _, _ -> failure ()
        end
      end

      | `TcCtt (ty, tc) ->
          if not (hastc env tvtc ty tc) then failure ()
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
           | None   -> t
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

  let fresh ?(tc = Sp.empty) ?ty ue = 
    let uid = EcUidgen.unique () in
      ue := { !ue with ue_uf = UF.set uid (tc, ty) (!ue).ue_uf; };
      tuni uid

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
  let uf = unify_core env (!ue).ue_tvtc (!ue).ue_uf t1 t2 in
    ue := { !ue with ue_uf = uf; }

(* -------------------------------------------------------------------- *)
let tfun_expected ue psig = 
  let tres = UniEnv.fresh ue in
    EcTypes.toarrow psig tres

let select_op ~preds tvi env name ue psig = 
  (* Filter operator based on given type variables instanciation *)
  let filter_on_tvi =
    let tvtc = (!ue).ue_tvtc in

    match tvi with
    | None -> fun _ -> true

    | Some (TVIunamed lt) ->
        let len = List.length lt in
          fun op ->
            let tparams = op.EcDecl.op_tparams in
               (List.length tparams = len)
            && (List.for_all2
                  (fun (_, tc) ty -> hastc env tvtc ty tc)
                  tparams lt)

    | Some (TVInamed ls) -> fun op ->
        let tparams = op.EcDecl.op_tparams in
        let for1 (s, ty) =
          match
            try  Some (List.find (fun (id, _) -> EcIdent.name id = s) tparams)
            with Not_found -> None
          with
          | None -> false
          | Some (_, tc) -> hastc env tvtc ty tc
        in
          List.for_all for1 ls
  in

  let fop op = (preds || not (EcDecl.is_pred op)) && filter_on_tvi op in
  let ops = EcEnv.Op.all fop name env in
  let select (path, op) =
    let subue = UniEnv.copy ue in
    let (top, tys) =
      UniEnv.openty subue op.EcDecl.op_tparams tvi (EcDecl.op_ty op)
    in
      try 
        let texpected = tfun_expected subue psig in
          unify env subue top texpected; 
          Some ((path, tys), top, subue) 
      with UnificationFailure _ -> None
  in
    List.pmap select ops
