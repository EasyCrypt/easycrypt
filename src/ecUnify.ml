(* -------------------------------------------------------------------- *)
open EcMaps
open EcUtils
open EcUidgen
open EcIdent
open EcTypes
open EcDecl

(* -------------------------------------------------------------------- *)
exception UnificationFailure of ty * ty
exception UninstanciateUni

(* -------------------------------------------------------------------- *)
module UFArgs = struct
  module I = struct
    type t = uid

    let equal   = uid_equal
    let compare = uid_compare
  end

  module D = struct
    type data    = ty option
    type effects = (ty * ty) list

    let default : data =
      None

    let isvoid (x : data) = (x = None)

    let noeffects : effects = []

    let union d1 d2 =
      match d1, d2 with
      | None, None -> (None, [])
      | None, d    -> (d   , [])
      | d, None    -> (d   , [])

      | Some ty1, Some ty2 -> (Some ty1, [ty1, ty2])
  end
end

module UF = EcUFind.Make(UFArgs.I)(UFArgs.D)

(* -------------------------------------------------------------------- *)
let unify_core (env : EcEnv.env) (uf : UF.t) t1 t2 =
  let failure () = raise (UnificationFailure (t1, t2)) in

  let ocheck uf i t =
    let map = Hint.create 0 in

    let rec doit t =
      match t.ty_node with
      | Tunivar i' when uid_equal i i'  -> true
      | Tunivar i' when Hint.mem map i' -> false
      | Tunivar i' -> begin
          match UF.data i' uf with
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

  let rec unify uf pb =
    let setvar i t =
      if ocheck uf i t then failure ();
      let (ti, effects) = UFArgs.D.union (UF.data i uf) (Some t) in
        (UF.set i ti uf, effects)
    in

    match pb with
    | [] -> uf

    | (t1, t2) :: pb ->
      let (uf, effects) =
        match ty_equal t1 t2 with
        | true  -> (uf, UFArgs.D.noeffects)
        | false -> begin
            match t1.ty_node, t2.ty_node with
            | Tunivar id1, Tunivar id2 ->
                if   not (uid_equal id1 id2)
                then UF.union id1 id2 uf
                else (uf, UFArgs.D.noeffects)
    
            | Tunivar id, _ -> setvar id t2
            | _, Tunivar id -> setvar id t1
      
            | Ttuple lt1, Ttuple lt2 ->
                if List.length lt1 <> List.length lt2 then failure ();
                (uf, List.combine lt1 lt2)
      
            | Tfun (t1, t2), Tfun (t1', t2') ->
                (uf, [(t1, t1'); (t2, t2')])
      
            | Tconstr (p1, lt1), Tconstr (p2, lt2) when EcPath.p_equal p1 p2 ->
                if List.length lt1 <> List.length lt2 then failure ();
                (uf, List.combine lt1 lt2)
    
            | Tconstr (p, lt), _ when EcEnv.Ty.defined p env ->
                (uf, [EcEnv.Ty.unfold p lt env, t2])
                
            | _, Tconstr (p, lt) when EcEnv.Ty.defined p env ->
                (uf, [t1, EcEnv.Ty.unfold p lt env])
      
            | Tglob mp1, Tglob mp2 ->
                let mp1 = EcEnv.NormMp.norm_tglob env mp1 in
                let mp2 = EcEnv.NormMp.norm_tglob env mp2 in
                  if   not (ty_equal mp1 mp2)
                  then failure ()
                  else (uf, UFArgs.D.noeffects)
      
            | _, _ -> raise (UnificationFailure (t1, t2))
        end
      in
        unify uf (effects @ pb)

  in
    unify uf [t1, t2]

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
           match UF.data i uf with
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
  ue_tuni   : Suid.t;
  ue_named  : EcIdent.t Mstr.t;
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

  let create vd =
    let ue = {
      ue_uf     = UF.initial;
      ue_tuni   = Suid.empty;
      ue_named  = Mstr.empty;
      ue_decl   = [];
      ue_closed = false;
    } in

    let ue =
      match vd with
      | None    -> ue
      | Some vd ->
          let vdmap = List.map (fun x -> (EcIdent.name x, x)) vd in
            { ue with
                ue_named  = Mstr.of_list vdmap;
                ue_decl   = List.rev vd;
                ue_closed = true; }
    in
      ref ue

  let fresh ue = 
    let uid = EcUidgen.unique () in
      ue := { !ue with ue_tuni = Suid.add uid (!ue).ue_tuni; };
      tuni uid

  let freshen_ue ue (params : ty_params) tvi = 
    match tvi with
    | None -> 
        List.fold_left
          (* FIXME: TC HOOK *)
          (fun s (v, _) -> Mid.add v (fresh ue) s) 
          Mid.empty params 

    | Some (TVIunamed lt) ->
        List.fold_left2
          (* FIXME: TC HOOK *)
          (fun s (v, _) t -> Mid.add v t s) Mid.empty
          params lt

    | Some (TVInamed l) ->
        (* FIXME: TC HOOK *)
        let for1 s (v, _) =
          let t =
            try  List.assoc (EcIdent.name v) l
            with Not_found -> fresh ue
          in
            Mid.add v t s
        in
          List.fold_left for1 Mid.empty params

  let subst_tv subst params = 
    (* FIXME: TC HOOK *)
    List.map (fun (tv, _) -> subst (tvar tv)) params

  let freshen ue params tvi ty = 
    let ue = copy ue in
    let subst = Tvar.subst (freshen_ue ue params tvi) in
      (ue, subst ty, subst_tv subst params)

  let freshendom ue params tvi dom = 
    let ue = copy ue in
    let subst = Tvar.subst (freshen_ue ue params tvi) in
      (ue, List.map subst dom, subst_tv subst params)

  let freshensig ue params tvi (dom, codom) = 
    let ue = copy ue in
    let subst = Tvar.subst (freshen_ue ue params tvi) in
      (ue, (List.map subst dom, subst codom), subst_tv subst params)

  let rec repr (ue : unienv) (t : ty) : ty = 
    match t.ty_node with
    | Tunivar id -> odfl t (UF.data id (!ue).ue_uf)
    | _ -> t

  let closed (ue : unienv) =
    UF.closed (!ue).ue_uf

  let close (ue : unienv) =
    if not (closed ue) then raise UninstanciateUni;
    (subst_of_uf (!ue).ue_uf)

  let assubst ue = subst_of_uf (!ue).ue_uf

  let tparams ue =
    (* FIXME: TC HOOK *)
    List.map (fun x -> (x, EcPath.Sp.empty)) (List.rev (!ue).ue_decl)
end

(* -------------------------------------------------------------------- *)
let unify env ue t1 t2 =
  let uf = unify_core env (!ue).ue_uf t1 t2 in
    ue := { !ue with ue_uf = uf; }

(* -------------------------------------------------------------------- *)
let filter_tvi = function 
  | None -> fun _ -> true

  | Some (TVIunamed l) -> 
      let len = List.length l in
        fun op -> List.length op.EcDecl.op_tparams = len

  | Some (TVInamed ls) -> fun op ->
      List.for_all
        (fun (s,_) -> 
          (* FIXME: TC HOOK *)
          List.exists (fun (id, _) -> EcIdent.name id = s)
            op.EcDecl.op_tparams)
        ls

let tfun_expected ue psig = 
  let tres = UniEnv.fresh ue in
    EcTypes.toarrow psig tres

let select_op pred tvi env name ue psig = 
  let fti = filter_tvi tvi in 
  let fop op = (pred || not (EcDecl.is_pred op)) && fti op in
  let ops = EcEnv.Op.all fop name env in
  let select (path, op) =
    let (subue, top, tys) =
      UniEnv.freshen ue op.EcDecl.op_tparams tvi (EcDecl.op_ty op)
    in
      try 
        let texpected = tfun_expected subue psig in
          unify env subue top texpected; 
          Some ((path, tys), top, subue) 
      with UnificationFailure _ -> None
  in
    List.pmap select ops
