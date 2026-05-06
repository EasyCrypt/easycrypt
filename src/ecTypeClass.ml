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

    (* Tunivar on the [ty] side is a wildcard: the goal type contains
       a fresh univar that the unifier will resolve later. Don't fail
       the match — leave the pattern's [Tvar] entries (if any) unbound
       and let the caller decide whether the partial match is enough. *)
    | _, Tunivar _ ->
      map

    | Tvar a, _ -> begin
      (* [a] may not be in [map] when the pattern carries free Tvars
         (e.g. an instance whose carrier was a section-local tparam
         that did not get generalised to [tci_params]). Treat that as
         a non-match rather than crashing the inference loop. *)
      match Mid.find_opt a map with
      | None -> raise NoMatch
      | Some None ->
        Mid.add a (Some ty) map

      | Some (Some ty') ->
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

    Some (TCIConcrete { path = p; etyargs = args; lift = []; })

  with Bailout | NoMatch -> None

(* -------------------------------------------------------------------- *)
and infer (env : EcEnv.env) (ty : ty) (tc : typeclass) =
  List.find_map_opt
    (check_tcinstance env ty tc)
    (EcEnv.TcInstance.get_all env)

(* -------------------------------------------------------------------- *)
(* Like [infer] but returns ALL matching instances as witnesses. Used
   to detect ambiguity (multi-flavor inheritance, e.g. a comring with
   both addmonoid- and mulmonoid-derived monoid views on the same
   carrier) — the caller may then defer commitment until other
   unification steps narrow the choice. *)
and infer_all (env : EcEnv.env) (ty : ty) (tc : typeclass) =
  List.filter_map
    (check_tcinstance env ty tc)
    (EcEnv.TcInstance.get_all env)

(* -------------------------------------------------------------------- *)
(* Build one [tcwitness] per entry of [tcs] for a carrier [body],
   suitable for plugging into the [tcwitness list] slot of an
   [add_tydef] binding. The expected witness for [body : tc] is
   queried via [infer]; if no instance is registered, falls back to
   a [`Abs body_path] / [`Var a] placeholder so the substitution
   matches the pre-fix shape. With this fallback the helper is
   non-failing — callers that want to error on a missing instance
   should check [infer] separately. *)
let witnesses_for_body
  (env : EcEnv.env) (body : ty) (tcs : typeclass list)
  : tcwitness list
=
  List.map (fun tc ->
    match infer env body tc with
    | Some w -> w
    | None ->
      let support =
        match body.ty_node with
        | Tvar a       -> `Var a
        | Tconstr (p, _) -> `Abs p
        | _ ->
          (* Last-ditch dummy; should never arise for sensible
             clone bodies, which are always [Tvar] or [Tconstr]. *)
          `Abs (EcPath.psymbol "?") in
      TCIAbstract { support; offset = 0; lift = [] }
  ) tcs

(* -------------------------------------------------------------------- *)
(* Match a candidate instance against [tc] on its arguments only,
   leaving the carrier ([tci.tci_type]) for the caller to unify with
   the goal carrier. Returns the partial type-substitution that
   pinned the [tci_params] from the match. *)
let candidates_by_args (env : EcEnv.env) (tc : typeclass)
  : (EcPath.path option * tcinstance * ty option EcIdent.Mid.t) list
=
  let try_one (p, tci) =
    match tci.tci_instance with
    | `General (tgp, _) when EcPath.p_equal tc.tc_name tgp.tc_name -> begin
      try
        let map =
          etyargs_match env (List.fst tci.tci_params)
            ~patterns:tgp.tc_args ~etyargs:tc.tc_args
        in Some (p, tci, map)
      with NoMatch -> None
      end
    | _ -> None
  in List.filter_map try_one (EcEnv.TcInstance.get_all env)

(* -------------------------------------------------------------------- *)
(* Flatten the parent DAG of a typeclass into a deduplicated list,
   self first. With single-inheritance this is the linear chain
   [tc; parent; grandparent; ...]; with multi-inheritance it's a
   BFS walk: [tc; parent_1; ...; parent_n; ...grandparents...].
   Each ancestor's [tc_args] is substituted along the path so the
   args reference [tc]'s tparams. Duplicates are dropped (an ancestor
   reachable via multiple paths appears once, at the shortest path). *)
let ancestors (env : EcEnv.env) (tc : typeclass) : typeclass list =
  let parents (tc : typeclass) : typeclass list =
    let decl = EcEnv.TypeClass.by_path tc.tc_name env in
    let subst =
      List.fold_left2
        (fun s (a, _) etyarg -> Mid.add a etyarg s)
        Mid.empty decl.tc_tparams tc.tc_args in
    List.map (fun (p, _ren) -> EcCoreSubst.Tvar.subst_tc subst p) decl.tc_prts in
  let same (a : typeclass) (b : typeclass) =
    EcPath.p_equal a.tc_name b.tc_name in
  let rec bfs (frontier : typeclass list) (acc : typeclass list) =
    match frontier with
    | [] -> List.rev acc
    | tc :: rest ->
      if List.exists (same tc) acc then bfs rest acc
      else bfs (rest @ parents tc) (tc :: acc)
  in bfs [tc] []

(* -------------------------------------------------------------------- *)
(* Compose two renamings.
   [outer] is declared on a parent edge: maps grandparent op names
     to parent op names (only listed entries are renamed; unlisted
     passes through identity).
   [inner] is the accumulated renaming on the child side: maps
     parent op names to child op names.
   Result: grandparent op names → child op names.

   Two cases:
   - For each (gp_name, p_name) in outer: child's name for that op
     is [inner(p_name)], defaulting to [p_name] if unlisted.
   - For each (p_name, c_name) in inner whose [p_name] is NOT
     referenced in outer (neither as a value nor as a key): the op
     passes through outer as identity, so grandparent's name for it
     is [p_name] and child's name is [c_name]. Add [(p_name, c_name)]. *)
let compose_renaming
  ~(outer : (EcSymbols.symbol * EcSymbols.symbol) list)
  ~(inner : (EcSymbols.symbol * EcSymbols.symbol) list)
  : (EcSymbols.symbol * EcSymbols.symbol) list
=
  let inner_map = EcMaps.Mstr.of_list inner in
  let from_outer =
    List.map
      (fun (gp_name, p_name) ->
        let c_name = odfl p_name (EcMaps.Mstr.find_opt p_name inner_map) in
        (gp_name, c_name))
      outer in
  let outer_p_names =
    List.fold_left (fun s (_, p) -> EcMaps.Sstr.add p s) EcMaps.Sstr.empty outer in
  let outer_gp_names =
    List.fold_left (fun s (gp, _) -> EcMaps.Sstr.add gp s) EcMaps.Sstr.empty outer in
  let from_inner =
    List.filter_map
      (fun (p_name, c_name) ->
        if EcMaps.Sstr.mem p_name outer_p_names || EcMaps.Sstr.mem p_name outer_gp_names
        then None
        else Some (p_name, c_name))
      inner in
  from_outer @ from_inner

(* -------------------------------------------------------------------- *)
(* True iff op [n] survives the cumulative ancestor→child renaming
   [ren] under the same name. An op is preserved when [ren] doesn't
   mention it (passes through as identity), or when it explicitly
   maps to itself. *)
let op_preserved
  (ren : (EcSymbols.symbol * EcSymbols.symbol) list)
  (n   : EcSymbols.symbol)
  : bool
=
  match List.assoc_opt n ren with
  | None    -> true
  | Some n' -> n = n'

(* -------------------------------------------------------------------- *)
(* Variant of [ancestors] that also returns the cumulative op renaming
   accumulated along the BFS walk from [tc] to each ancestor. The
   renaming maps the ancestor's op names to the corresponding op
   names declared in (or inherited by) [tc]. *)
let ancestors_with_renaming
  (env : EcEnv.env) (tc : typeclass)
  : (typeclass * (EcSymbols.symbol * EcSymbols.symbol) list) list
=
  let parents tc =
    let decl = EcEnv.TypeClass.by_path tc.tc_name env in
    let subst =
      List.fold_left2
        (fun s (a, _) etyarg -> Mid.add a etyarg s)
        Mid.empty decl.tc_tparams tc.tc_args in
    List.map
      (fun (p, ren) -> (EcCoreSubst.Tvar.subst_tc subst p, ren))
      decl.tc_prts in
  (* Compose two renamings.
     [outer] is declared on a parent edge: maps grandparent op names
       to parent op names (only listed entries are renamed; unlisted
       passes through identity).
     [inner] is the accumulated renaming on the child side: maps
       parent op names to child op names.
     Result: grandparent op names → child op names.

     Two cases:
     - For each (gp_name, p_name) in outer: child's name for that op
       is [inner(p_name)], defaulting to [p_name] if unlisted.
     - For each (p_name, c_name) in inner whose [p_name] is NOT
       referenced in outer (neither as a value nor as a key): the op
       passes through outer as identity, so grandparent's name for it
       is [p_name] and child's name is [c_name]. Add [(p_name, c_name)]. *)
  let compose = compose_renaming in
  let ren_eq r1 r2 =
    List.length r1 = List.length r2
    && List.for_all2 (fun (a, b) (c, d) -> a = c && b = d) r1 r2 in
  let same (a, ra) (b, rb) =
    EcPath.p_equal a.tc_name b.tc_name && ren_eq ra rb in
  let rec bfs frontier acc =
    match frontier with
    | [] -> List.rev acc
    | (tc, ren) :: rest ->
      if List.exists (same (tc, ren)) acc then bfs rest acc
      else
        let next =
          List.map
            (fun (p, p_ren) -> (p, compose ~outer:p_ren ~inner:ren))
            (parents tc) in
        bfs (rest @ next) ((tc, ren) :: acc)
  in bfs [(tc, [])] []
