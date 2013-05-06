(* -------------------------------------------------------------------- *)
open EcMaps
open EcUtils
open EcUidgen
open EcIdent
open EcTypes

(* -------------------------------------------------------------------- *)
exception TypeVarCycle of uid * ty
exception UnificationFailure of ty * ty
exception UninstanciateUni of uid
exception DuplicateTvar of EcSymbols.symbol

type unienv = 
    { mutable unival  : ty Muid.t;
      mutable unidecl : Suid.t;
      mutable varval  : EcIdent.t Mstr.t;
      mutable vardecl : EcIdent.t list;
      mutable strict  : bool;
    } 

module UniEnv = struct
  type tvar_inst_kind = 
    | TVIunamed of ty list
    | TVInamed  of (EcSymbols.symbol * ty) list

  type tvi = tvar_inst_kind option

  let empty () = 
    { unival  = Muid.empty;
      unidecl = Suid.empty;
      varval  = Mstr.empty;
      vardecl = [];
      strict  = false;
    }

  let get_var ue s = 
    try Mstr.find s ue.varval 
    with _ ->
      if ue.strict then raise Not_found;
      let id = EcIdent.create s in
      ue.varval <- Mstr.add s id ue.varval;
      ue.vardecl <- id :: ue.vardecl;
      id

  let create vd =
    let ue = empty () in
    let add id =
      ue.varval <- Mstr.add (EcIdent.name id) id ue.varval;
      ue.vardecl <- id :: ue.vardecl in
    match vd with
    | None -> ue
    | Some l -> List.iter add l; ue.strict <- true; ue
        
  let copy (ue : unienv) =
    { unival  = ue.unival;
      unidecl = ue.unidecl;
      varval  = ue.varval;
      vardecl = ue.vardecl;
      strict  = ue.strict;
    }

  let fresh_uid ue = 
    let uid = EcUidgen.unique () in
    ue.unidecl <- Suid.add uid ue.unidecl;
    tuni uid

  let init_freshen ue params tvi = 
    let ue = copy ue in
    let s = 
      match tvi with
      | None -> 
          List.fold_left (fun s v -> Mid.add v (fresh_uid ue) s) 
            Mid.empty params 
      | Some (TVIunamed lt) ->
          List.fold_left2 (fun s v t -> Mid.add v t s) Mid.empty params lt
      | Some(TVInamed l) ->
          List.fold_left (fun s v ->
            let t = try List.assoc (EcIdent.name v) l with _ -> fresh_uid ue in
            Mid.add v t s) Mid.empty params in
    ue, Tvar.subst s
    
  let subst_tv subst params = 
    List.map (fun tv -> subst (tvar tv)) params

  let freshen ue params tvi ty = 
    let ue, subst = init_freshen ue params tvi in
    ue, subst ty, subst_tv subst params

  let freshendom ue params tvi dom = 
    let ue, subst = init_freshen ue params tvi in
    ue, List.map subst dom, subst_tv subst params

  let freshensig ue params tvi (dom, codom) = 
    let ue, subst = init_freshen ue params tvi in
    ue, (List.map subst dom, subst codom), subst_tv subst params

  let restore ~(dst:unienv) ~(src:unienv) =
    dst.unival <- src.unival;
    dst.unidecl <- src.unidecl

  let dump pp (ue : unienv) =
    let pp_binding pp (a, ty) =
      EcDebug.onhlist pp (string_of_int a)
        (EcTypes.Dump.ty_dump) [ty]
    in
      EcDebug.onhseq
        pp "Unification Environment" pp_binding
        (EcUidgen.Muid.to_stream ue.unival)

  let rec repr (ue : unienv) (t : ty) : ty = 
    match t.ty_node with
    | Tunivar id -> odfl t (Muid.find_opt id ue.unival)
    | _ -> t

  let bind (ue : unienv) id t =
    assert (Suid.mem id ue.unidecl);
    match t.ty_node with
    | Tunivar id' when uid_equal id id' -> ()
    | _ ->
        let uv = ue.unival in 
        assert (not (Muid.mem id uv));
        let t = Tuni.subst uv t in
        if Tuni.occur id t then raise (TypeVarCycle (id, t));
        ue.unival <- 
          Muid.add id t
            (Muid.map (Tuni.subst1 (id, t)) uv)

  let close (ue:unienv) =
    let diff = Muid.diff (fun _ _ _ -> None) ue.unidecl ue.unival in
    if not (Muid.is_empty diff) then 
      raise (UninstanciateUni (fst (Muid.choose diff)));
    ue.unival

  let asmap ue = ue.unival

  let tparams ue = List.rev ue.vardecl

end

(* -------------------------------------------------------------------- *)
let unify (env : EcEnv.env) (ue : unienv) =
  let rec unify (t1 : ty) (t2 : ty) = 
    let r1, r2 = UniEnv.repr ue t1, UniEnv.repr ue t2 in 
    match r1.ty_node, r2.ty_node with
    | Tvar i1, Tvar i2 -> 
        (* FIXME use equal *)
        if not (EcIdent.id_equal i1 i2) then 
          raise (UnificationFailure (t1, t2))

    | Tunivar id, _ -> UniEnv.bind ue id r2
    | _, Tunivar id -> UniEnv.bind ue id r1

    | Ttuple lt1, Ttuple lt2 ->
        if List.length lt1 <> List.length lt2 then 
          raise (UnificationFailure (t1, t2));
        List.iter2 unify lt1 lt2

    | Tfun(t1,t2), Tfun(t1',t2') ->
        unify t1 t1'; unify t2 t2'

    | Tconstr(p1, lt1), Tconstr(p2, lt2) when EcPath.p_equal p1 p2 ->
        if List.length lt1 <> List.length lt2 then
          raise (UnificationFailure (t1, t2));
        List.iter2 unify lt1 lt2

    | Tconstr(p, lt), _ when EcEnv.Ty.defined p env ->
        unify (EcEnv.Ty.unfold p lt env) r2

    | _, Tconstr(p, lt) when EcEnv.Ty.defined p env ->
        unify r1 (EcEnv.Ty.unfold p lt env)
    

    | _, _ -> raise (UnificationFailure(t1, t2))

  in
    unify

(* -------------------------------------------------------------------- *)
let filter_tvi = function 
  | None -> fun _ -> true
  | Some (UniEnv.TVIunamed l) -> 
      let len = List.length l in
      fun op -> List.length op.EcDecl.op_tparams = len
  | Some (UniEnv.TVInamed ls) -> fun op ->
      List.for_all 
        (fun (s,_) -> 
          List.exists (fun id -> EcIdent.name id = s) op.EcDecl.op_tparams) ls

let tfun_expected ue psig = 
  let tres = UniEnv.fresh_uid ue in
  EcTypes.toarrow psig tres

let select_op pred tvi env name ue psig = 
  let fti = filter_tvi tvi in 
  let fop op =
    (pred || not (EcDecl.is_pred op)) && 
    fti op in
  let ops = EcEnv.Op.all fop name env in
  let select (path, op) = 
    let subue,top, tys = 
      UniEnv.freshen ue op.EcDecl.op_tparams tvi (EcDecl.op_ty op) in
    try 
      let texpected = tfun_expected subue psig in
      unify env subue top texpected; 
      Some ((path,tys), top, subue) 
    with _ -> None in
  List.pmap select ops
