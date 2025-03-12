open EcAst
open EcTypes
open EcModules
open EcSymbols

(*---------------------------------------------------------------------------------------*)
type u_error =
  | UE_AliasNoRet
  | UE_AliasNotPv
  | UE_InvalidRetInstr
  | UE_AbstractFun
  | UE_TypeMismatch of expr * expr
  | UE_UnificationFailArg of symbol
  | UE_UnificationFailPv of symbol
  | UE_LvNotInLockstep of lvalue * lvalue
  | UE_ExprNotInLockstep of expr * expr
  | UE_InstrNotInLockstep of instr * instr
  | UE_DifferentProgramLengths of stmt * stmt

exception UnificationError of u_error

(*---------------------------------------------------------------------------------------*)
type u_value =
  | Arg of expr option
  | Local of prog_var option

type umap = u_value Msym.t

(*---------------------------------------------------------------------------------------*)
let rec unify_exprs umap e1 e2 =
  if not (EcTypes.ty_equal e1.e_ty e2.e_ty) then
    raise (UnificationError (UE_TypeMismatch (e1, e2)));

  match e1.e_node, e2.e_node with
  | Eint x1, Eint x2 when EcBigInt.equal x1 x2 -> umap
  | Elocal _, Elocal _ -> umap
  | Evar (PVloc v), Evar pv ->

    let update value =
      match value with
      | Some (Local None) -> Some (Local (Some pv))
      | Some (Arg None) -> Some (Arg (Some e2))
      | _ -> value
    in
    Msym.change update v umap

  | Evar (PVloc v), _ ->
    (* NOTE: Only the arguments can unify with compound expressions *)
    let update value =
      match value with
      | None ->
        raise (UnificationError (UE_ExprNotInLockstep (e1, e2)))
      | Some (Arg None) -> Some (Arg (Some e2))
      | _ -> value
    in
    Msym.change update v umap
  | Evar (PVglob xp1), Evar (PVglob xp2)
    when EcPath.x_equal xp1 xp2 -> umap
  | Eop (p1, _), Eop (p2, _)
    when EcPath.p_equal p1 p2 -> umap
  | Eapp (f1, a1), Eapp (f2, a2) ->
    let umap = unify_exprs umap f1 f2 in
    if List.length a1 <> List.length a2 then
      raise (UnificationError (UE_ExprNotInLockstep (e1, e2)));
    List.fold_left2 (fun umap e1 e2 -> unify_exprs umap e1 e2) umap a1 a2
  | Equant (q1, b1, e1), Equant (q2, b2, e2) when q1 = q2 ->
    if List.length b1 <> List.length b2 then
      raise (UnificationError (UE_ExprNotInLockstep (e1, e2)));
    unify_exprs umap e1 e2
  | Elet (_, e1, u1), Elet (_, e2, u2) ->
    let umap = unify_exprs umap e1 e2 in
    unify_exprs umap u1 u2
  | Etuple t1, Etuple t2 ->
    List.fold_left (fun umap (e1, e2) -> unify_exprs umap e1 e2) umap (List.combine t1 t2)
  | Eif (c1, t1, f1), Eif (c2, t2, f2) ->
    let umap = unify_exprs umap c1 c2 in
    let umap = unify_exprs umap t1 t2 in
    unify_exprs umap f1 f2
  | Ematch (c1, p1, _), Ematch (c2, p2, _) ->
    let umap = unify_exprs umap c1 c2 in
    if List.length p1 <> List.length p2 then
      raise (UnificationError (UE_ExprNotInLockstep (e1, e2)));
    List.fold_left2 (fun umap e1 e2 -> unify_exprs umap e1 e2) umap p1 p2
  | Eproj (e1, x1), Eproj (e2, x2) when x1 = x2 ->
    unify_exprs umap e1 e2
  | _ -> raise (UnificationError (UE_ExprNotInLockstep (e1, e2)))

(*---------------------------------------------------------------------------------------*)
let unify_lv umap lv1 lv2 =
  let update umap v pv t =
    let doit x =
      match x with
      | Some (Local None) -> Some (Local (Some pv))
      | Some (Arg None) -> Some (Arg (Some (e_var pv t)))
      | _ -> x
    in
    Msym.change doit v umap
  in

  match lv1, lv2 with
  | LvVar (PVglob xp1, _), LvVar (PVglob xp2, _)
    when EcPath.x_equal xp1 xp2 -> umap
  | LvVar (PVloc v, _), LvVar (pv, t) ->
    update umap v pv t
  | LvTuple pvs1, LvTuple pvs2 ->
    if List.length pvs1 <> List.length pvs2 then
      raise (UnificationError (UE_LvNotInLockstep (lv1, lv2)));

    List.fold_left2 (fun umap (pv1, _) (pv2, t) ->
      match pv1, pv2 with
      | PVglob xp1, PVglob xp2
        when EcPath.x_equal xp1 xp2 -> umap
      | PVloc v, pv ->
        update umap v pv t
      | _ -> raise (UnificationError (UE_LvNotInLockstep (lv1, lv2)))
      )
      umap
      pvs1
      pvs2
  | _, _ -> raise (UnificationError (UE_LvNotInLockstep (lv1, lv2)))

(*---------------------------------------------------------------------------------------*)
let rec unify_instrs umap i1 i2 =
 match i1.i_node, i2.i_node with
  | Sasgn(lv1, e1), Sasgn(lv2, e2)
  | Srnd(lv1, e1), Srnd(lv2, e2) ->
    let umap = unify_lv umap lv1 lv2 in
    unify_exprs umap e1 e2

  | Scall(olv1, xp1, args1), Scall(olv2, xp2, args2) when EcPath.x_equal xp1 xp2 ->
    let umap =
      match olv1, olv2 with
      | Some lv1, Some lv2 -> unify_lv umap lv1 lv2
      | None, None -> umap
      | _, _ -> raise (UnificationError (UE_InstrNotInLockstep (i1, i2)));
    in

    let args1, args2 =
      match args1, args2 with
      | _, _ when List.length args1 = List.length args2 -> args1, args2
      | [al], _ -> begin
        match al.e_node with
        | Etuple args1 -> args1, args2
        | _ -> raise (UnificationError (UE_InstrNotInLockstep (i1, i2)))
      end
      | _, [ar] -> begin
      match ar.e_node with
        | Etuple args2 -> args1, args2
        | _ -> raise (UnificationError (UE_InstrNotInLockstep (i1, i2)))
      end
      | _, _ -> raise (UnificationError (UE_InstrNotInLockstep (i1, i2)))
    in

    List.fold_left (fun umap (e1, e2) -> unify_exprs umap e1 e2) umap (List.combine args1 args2)

  | Sif(e1, st1, sf1), Sif(e2, st2, sf2) ->
    let umap = unify_exprs umap e1 e2 in
    let umap = unify_stmts umap st1 st2 in
    unify_stmts umap sf1 sf2

  | Swhile(e1, s1), Swhile(e2, s2) ->
    let umap = unify_exprs umap e1 e2 in
    unify_stmts umap s1 s2

  | Smatch(e1, bs1), Smatch(e2, bs2) ->
    let umap = unify_exprs umap e1 e2 in
    List.fold_left2 (fun umap (p1, b1) (p2, b2) ->
      if List.length p1 <> List.length p2 then
        raise (UnificationError (UE_InstrNotInLockstep (i1, i2)));
      unify_stmts umap b1 b2
    ) umap bs1 bs2

  | Sassert e1, Sassert e2 ->
    unify_exprs umap e1 e2

  | Sabstract x1, Sabstract x2 when EcIdent.id_equal x1 x2 -> umap

  | _ -> raise (UnificationError (UE_InstrNotInLockstep (i1, i2)));

and unify_stmts (umap : umap) s1 s2 =
  let s1n, s2n = s1.s_node, s2.s_node in
  if List.length s1n <> List.length s2n then
    raise (UnificationError (UE_DifferentProgramLengths (s1, s2)));
  List.fold_left2 (fun umap i1 i2 -> unify_instrs umap i1 i2) umap s1n s2n

(*---------------------------------------------------------------------------------------*)
let unify_func env mode fname s =
  let f = EcEnv.Fun.by_xpath fname env in
  let fdef =
    match f.f_def with
    | FBdef d -> d
    | _ -> raise (UnificationError UE_AbstractFun)
  in

  let args = List.filter_map ov_name f.f_sig.fs_anames in
  let locals = List.map v_name fdef.f_locals in

  let umap = List.fold_left (fun umap a -> Msym.add a (Arg None) umap) Msym.empty args in
  let umap = List.fold_left (fun umap a -> Msym.add a (Local None) umap) umap locals in

  let close_args umap args =
    List.map (fun a ->
        match Msym.find a umap with
        | Arg (Some e) -> e
        | _ -> raise (UnificationError (UE_UnificationFailArg a))
      )
      args
  in

  match mode, fdef.f_ret with
  | `Exact, None ->
    let umap = unify_stmts umap fdef.f_body s in
    s_call (None, fname, close_args umap args)
  | `Exact, Some re -> begin
    match EcLowPhlGoal.s_last destr_asgn s with
    | None -> raise (UnificationError UE_InvalidRetInstr)
    | Some ((lv, e), s) ->
      let umap = unify_stmts umap fdef.f_body s in
      let umap = unify_exprs umap re e in
      let args = close_args umap args in
      s_call (Some lv, fname, args)
    end
  | `Alias, None ->
    raise (UnificationError UE_AliasNoRet)
  | `Alias, Some e ->
    if not (is_tuple_var e || is_var e) then
      raise (UnificationError UE_AliasNotPv);
    let umap = unify_stmts umap fdef.f_body s in
    let args = close_args umap args in
    let alias =
      let pvs = lv_to_ty_list (lv_of_expr e) in
      let pvs =
        List.map
          (fun (pv, t) ->
            if is_loc pv then
              match Msym.find (get_loc pv) umap with
              | Arg (Some e) when is_var e -> destr_var e, e.e_ty
              | Local (Some pv) -> pv, t
              | _ -> raise (UnificationError (UE_UnificationFailPv (get_loc pv)))
            else
              pv, t
          )
          pvs
      in
      lv_of_list pvs
    in
    s_call (alias, fname, args)

