(* -------------------------------------------------------------------- *)
open EcIdent
open EcPath
open EcUtils
open EcAst
open EcTheory

(* -------------------------------------------------------------------- *)
exception NoMatch

(* -------------------------------------------------------------------- *)
module TyMatch(E : sig val env : EcEnv.env end) = struct
  let rec doit_type (map : ty option Mid.t) (pattern : ty) (ty : ty) =
    let pattern = EcEnv.ty_hnorm pattern E.env in
    let ty = EcEnv.ty_hnorm ty E.env in

    match pattern.ty_node, ty.ty_node with
    | Tunivar _, _ ->
      assert false

    | Tvar a, _ -> begin
      match Option.get (Mid.find_opt a map) with
      | None ->
        Mid.add a (Some ty) map
        
      | Some ty' ->
        if not (EcCoreEqTest.for_type E.env ty ty') then
          raise NoMatch;
        map

    end

    | Tglob id1, Tglob id2 when EcIdent.id_equal id1 id2 ->
      map

    | Tconstr (p, args), Tconstr (p', args') ->
      if not (EcPath.p_equal p p') then
        raise NoMatch;
      doit_etyargs map args args'

    | Ttuple ptns, Ttuple tys when List.length ptns = List.length tys ->
      doit_types map ptns tys

    | Tfun (p1, p2), Tfun (ty1, ty2) ->
      doit_types map [p1; p2] [ty1; ty2]

    | _, _ ->
      raise NoMatch

  and doit_types (map : ty option Mid.t) (pts : ty list) (tys : ty list) =    
    List.fold_left2 doit_type map pts tys

  and doit_etyarg (map : ty option Mid.t) ((pattern, ptcws) : etyarg) ((ty, ttcws) : etyarg) =
    let map = doit_type map pattern ty in
    let map = doit_tcws map ptcws ttcws in
    map

  and doit_etyargs (map : ty option Mid.t) (pts : etyarg list) (etys : etyarg list) =
    List.fold_left2 doit_etyarg map pts etys

  and doit_tcw (map : ty option Mid.t) (ptcw : tcwitness) (ttcw : tcwitness) =
    match ptcw, ttcw with
    | TCIUni _, _ ->
      assert false

    | TCIConcrete ptcw, TCIConcrete ttcw ->
      if not (EcPath.p_equal ptcw.path ttcw.path) then
        raise NoMatch;
      doit_etyargs map ptcw.etyargs ttcw.etyargs

    | TCIAbstract _, TCIAbstract _ ->
      if not (EcAst.tcw_equal ptcw ttcw) then
        raise NoMatch;
      map

    | _, _ ->
      raise NoMatch

  and doit_tcws (map : ty option Mid.t) (ptcws : tcwitness list) (ttcws : tcwitness list) =
    List.fold_left2 doit_tcw map ptcws ttcws
end

(* -------------------------------------------------------------------- *)
let ty_match (env : EcEnv.env) (params : ident list) ~(pattern : ty) ~(ty : ty) =
  let module M = TyMatch(struct let env = env end) in
  let map = Mid.of_list (List.map (fun a -> (a, None)) params) in
  M.doit_type map pattern ty

(* -------------------------------------------------------------------- *)
let etyargs_match
   (env      : EcEnv.env)
   (params   : ident list)
  ~(patterns : etyarg list)
  ~(etyargs  : etyarg list)
=
  let module M = TyMatch(struct let env = env end) in
  let map = Mid.of_list (List.map (fun a -> (a, None)) params) in
  M.doit_etyargs map patterns etyargs

(* -------------------------------------------------------------------- *)
let rec check_tcinstance
  (env      : EcEnv.env)
  (ty       : ty)
  (tc       : typeclass)
  ((p, tci) : path option * tcinstance)
=
  let exception Bailout in

  try
    let p = oget ~exn:Bailout p in

    let tgargs =
      match tci.tci_instance with
      | `General (tgp, _) ->
        if not (EcPath.p_equal tc.tc_name tgp.tc_name) then
          raise Bailout;
        tgp.tc_args
      | _ -> raise Bailout in

    let map =
      etyargs_match env (List.fst tci.tci_params)
        ~patterns:tgargs ~etyargs:tc.tc_args in

    let map =
      let module M = TyMatch(struct let env = env end) in
      M.doit_type map tci.tci_type ty in


    let _, args = List.fold_left_map (fun subst (a, aargs) ->
      let aty = oget ~exn:Bailout (Mid.find a map) in
      let aargs = List.map (fun aarg ->
          let aarg = EcCoreSubst.Tvar.subst_tc subst aarg in
          oget ~exn:Bailout (infer env aty aarg)
        ) aargs in
      let subst = Mid.add a (aty, aargs) subst in
      (subst, (aty, aargs))
    ) Mid.empty tci.tci_params in

    Some (TCIConcrete { path = p; etyargs = args; })

  with Bailout | NoMatch -> None

(* -------------------------------------------------------------------- *)
and infer (env : EcEnv.env) (ty : ty) (tc : typeclass) =
  List.find_map_opt
    (check_tcinstance env ty tc)
    (EcEnv.TcInstance.get_all env)
