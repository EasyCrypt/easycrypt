(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcUtils
open EcIdent
open EcPath
open EcTypes
open EcModules
open EcFol
open EcEnv

module BI = EcBigInt

(* -------------------------------------------------------------------- *)
exception IncompatibleType of env * (ty * ty)
exception IncompatibleForm of env * (form * form)

(* -------------------------------------------------------------------- *)
type 'a eqtest  = env -> 'a -> 'a -> bool
type 'a eqntest = env -> ?norm:bool -> 'a -> 'a -> bool

module EqTest = struct
  let rec for_type env t1 t2 =
    ty_equal t1 t2 || for_type_r env t1 t2

  and for_type_r env t1 t2 =
    match t1.ty_node, t2.ty_node with
    | Tunivar uid1, Tunivar uid2 -> EcUid.uid_equal uid1 uid2

    | Tvar i1, Tvar i2 -> i1 = i2

    | Ttuple lt1, Ttuple lt2 ->
          List.length lt1 = List.length lt2
       && List.all2 (for_type env) lt1 lt2

    | Tfun (t1, t2), Tfun (t1', t2') ->
        for_type env t1 t1' && for_type env t2 t2'

    | Tglob mp, _ when EcEnv.NormMp.tglob_reducible env mp ->
        for_type env (EcEnv.NormMp.norm_tglob env mp) t2

    | _, Tglob mp when EcEnv.NormMp.tglob_reducible env mp ->
        for_type env t1 (EcEnv.NormMp.norm_tglob env mp)

    | Tconstr (p1, lt1), Tconstr (p2, lt2) when EcPath.p_equal p1 p2 ->
        if
             List.length lt1 = List.length lt2
          && List.all2 (for_type env) lt1 lt2
        then true
        else
          if   Ty.defined p1 env
          then for_type env (Ty.unfold p1 lt1 env) (Ty.unfold p2 lt2 env)
          else false

    | Tconstr(p1,lt1), _ when Ty.defined p1 env ->
        for_type env (Ty.unfold p1 lt1 env) t2

    | _, Tconstr(p2,lt2) when Ty.defined p2 env ->
        for_type env t1 (Ty.unfold p2 lt2 env)

    | _, _ -> false

  (* ------------------------------------------------------------------ *)
  let is_unit env ty = for_type env tunit ty
  let is_bool env ty = for_type env tbool ty
  let is_int  env ty = for_type env tint  ty

  (* ------------------------------------------------------------------ *)
  let for_type_exn env t1 t2 =
    if not (for_type env t1 t2) then
      raise (IncompatibleType (env, (t1, t2)))

  (* ------------------------------------------------------------------ *)
  let for_pv env ~norm p1 p2 =
    pv_equal p1 p2 || (norm && (p1.pv_kind = p2.pv_kind) &&
      let p1 = NormMp.norm_pvar env p1 in
      let p2 = NormMp.norm_pvar env p2 in
      EcPath.x_equal p1.pv_name p2.pv_name)

  (* ------------------------------------------------------------------ *)
  let for_xp env ~norm p1 p2 =
     EcPath.x_equal p1 p2 || (norm &&
       let p1 = NormMp.norm_xfun env p1 in
       let p2 = NormMp.norm_xfun env p2 in
       EcPath.x_equal p1 p2)

  (* ------------------------------------------------------------------ *)
  let for_mp env ~norm p1 p2 =
     EcPath.m_equal p1 p2 || (norm &&
       let p1 = NormMp.norm_mpath env p1 in
       let p2 = NormMp.norm_mpath env p2 in
       EcPath.m_equal p1 p2)

  (* ------------------------------------------------------------------ *)
  let for_expr env ~norm =
    let module E = struct exception NotConv end in

    let find alpha id = odfl id (Mid.find_opt id alpha) in

    let noconv (f : expr -> expr -> bool) e1 e2 =
      try f e1 e2 with E.NotConv -> false in

    let check_binding env alpha (id1, ty1) (id2, ty2) =
      if not (for_type env ty1 ty2) then
        raise E.NotConv;
      Mid.add id1 id2 alpha in

    let check_bindings env alpha b1 b2 =
      if List.length b1 <> List.length b2 then
        raise E.NotConv;
      List.fold_left2 (check_binding env) alpha b1 b2 in

    let check_lpattern alpha lp1 lp2 =
      match lp1, lp2 with
      | LSymbol (id1,_), LSymbol (id2,_) ->
          Mid.add id1 id2 alpha

      | LTuple lid1, LTuple lid2 when List.length lid1 = List.length lid2 ->
          List.fold_left2
            (fun alpha (id1,_) (id2,_) -> Mid.add id1 id2 alpha)
            alpha lid1 lid2

      | _, _ -> raise E.NotConv in

    let rec aux alpha e1 e2 =
      e_equal e1 e2 || aux_r alpha e1 e2

    and aux_r alpha e1 e2 =
      match e1.e_node, e2.e_node with
      | Eint i1, Eint i2 ->
          BI.equal i1 i2

      | Elocal id1, Elocal id2 ->
          EcIdent.id_equal (find alpha id1) id2

      | Evar p1, Evar p2 ->
          for_pv env ~norm p1 p2

      | Eop(o1,ty1), Eop(o2,ty2) ->
          p_equal o1 o2 && List.all2 (for_type env) ty1 ty2

      | Equant(q1,b1,e1), Equant(q2,b2,e2) when qt_equal q1 q2 ->
          let alpha = check_bindings env alpha b1 b2 in
          noconv (aux alpha) e1 e2

      | Eapp (f1, args1), Eapp (f2, args2) ->
          aux alpha f1 f2 && List.all2 (aux alpha) args1 args2

      | Elet (p1, f1', g1), Elet (p2, f2', g2) ->
          aux alpha f1' f2'
            && noconv (aux (check_lpattern alpha p1 p2)) g1 g2

      | Etuple args1, Etuple args2 -> List.all2 (aux alpha) args1 args2

      | Eif (a1,b1,c1), Eif(a2,b2,c2) ->
          aux alpha a1 a2 && aux alpha b1 b2 && aux alpha c1 c2

      | Ematch (e1,es1,ty1), Ematch(e2,es2,ty2) ->
          for_type env ty1 ty2
            && List.all2 (aux alpha) (e1::es1) (e2::es2)

      | _, _ -> false

    in fun alpha e1 e2 -> aux alpha e1 e2

  (* ------------------------------------------------------------------ *)
  let for_lv env ~norm lv1 lv2 =
    match lv1, lv2 with
    | LvVar(p1, _), LvVar(p2, _) ->
        for_pv env ~norm p1 p2

    | LvTuple p1, LvTuple p2 ->
        List.all2
          (fun (p1, _) (p2, _) -> for_pv env ~norm p1 p2)
          p1 p2

    | _, _ -> false

  (* ------------------------------------------------------------------ *)
  let rec for_stmt env alpha ~norm s1 s2 =
       s_equal s1 s2
    || List.all2 (for_instr env alpha ~norm) s1.s_node s2.s_node

  (* ------------------------------------------------------------------ *)
  and for_instr env alpha ~norm i1 i2 =
    i_equal i1 i2 || for_instr_r env alpha ~norm i1 i2

  and for_instr_r env alpha ~norm i1 i2 =
    match i1.i_node, i2.i_node with
    | Sasgn (lv1, e1), Sasgn (lv2, e2) ->
           for_lv env ~norm lv1 lv2
        && for_expr env alpha ~norm e1 e2

    | Srnd (lv1, e1), Srnd (lv2, e2) ->
           for_lv env ~norm lv1 lv2
        && for_expr env alpha ~norm e1 e2

    | Scall (lv1, f1, e1), Scall (lv2, f2, e2) ->
        oall2 (for_lv env ~norm) lv1 lv2
          && for_xp env ~norm f1 f2
          && List.all2 (for_expr env alpha ~norm) e1 e2

    | Sif (a1, b1, c1), Sif(a2, b2, c2) ->
        for_expr env alpha ~norm a1 a2
          && for_stmt env alpha ~norm b1 b2
          && for_stmt env alpha ~norm c1 c2

    | Swhile(a1,b1), Swhile(a2,b2) ->
           for_expr env alpha ~norm a1 a2
        && for_stmt env alpha ~norm b1 b2

    | Smatch(e1,bs1), Smatch(e2,bs2)
        when List.length bs1 = List.length bs2
      -> begin
        let module E = struct exception NotConv end in

        let check_branch (xs1, s1) (xs2, s2) =
          if List.length xs1 <> List.length xs2 then
            raise E.NotConv;
          let alpha =
            let rec do1 alpha (id1, ty1) (id2, ty2) =
              if not (for_type env ty1 ty2) then
                raise E.NotConv;
              Mid.add id1 id2 alpha in
            List.fold_left2 do1 alpha xs1 xs2
          in for_stmt env alpha ~norm s1 s2 in

        try
             for_expr env alpha ~norm e1 e2
          && List.all2 (check_branch) bs1 bs2
        with E.NotConv -> false
      end

    | Sassert a1, Sassert a2 ->
        for_expr env alpha ~norm a1 a2

    | Sabstract id1, Sabstract id2 ->
        EcIdent.id_equal id1 id2

    | _, _ -> false

  (* ------------------------------------------------------------------ *)
  let for_pv    = fun env ?(norm = true) -> for_pv    env ~norm
  let for_xp    = fun env ?(norm = true) -> for_xp    env ~norm
  let for_mp    = fun env ?(norm = true) -> for_mp    env ~norm
  let for_instr = fun env ?(norm = true) -> for_instr env Mid.empty ~norm
  let for_stmt  = fun env ?(norm = true) -> for_stmt  env Mid.empty ~norm
  let for_expr  = fun env ?(norm = true) -> for_expr  env Mid.empty ~norm
end

(* -------------------------------------------------------------------- *)
exception NotConv

let ensure b = if b then () else raise NotConv

let check_ty env subst ty1 ty2 =
  ensure (EqTest.for_type env ty1 (subst.fs_ty ty2))

let add_local (env, subst) (x1, ty1) (x2, ty2) =
  check_ty env subst ty1 ty2;
  env,
  if id_equal x1 x2 then subst
  else Fsubst.f_bind_rename subst x2 x1 ty1

let check_lpattern env subst lp1 lp2 =
    match lp1, lp2 with
    | LSymbol xt1, LSymbol xt2 -> add_local (env, subst) xt1 xt2
    | LTuple lid1, LTuple lid2 when List.length lid1 = List.length lid2 ->
      List.fold_left2 add_local (env,subst) lid1 lid2
    | _, _ -> raise NotConv

let check_memtype env mt1 mt2 =
  match mt1, mt2 with
  | None, None -> ()
  | Some lmt1, Some lmt2 ->
    let xp1, xp2 = EcMemory.lmt_xpath lmt1, EcMemory.lmt_xpath lmt2 in
    ensure (EqTest.for_xp env xp1 xp2);
    let m1, m2 = EcMemory.lmt_bindings lmt1, EcMemory.lmt_bindings lmt2 in
    ensure (EcSymbols.Msym.equal
              (fun (p1,ty1) (p2,ty2) ->
                p1 = p2 && EqTest.for_type env ty1 ty2) m1 m2)
  | _, _ -> raise NotConv

let check_binding (env, subst) (x1, gty1) (x2, gty2) =
  let gty2 = Fsubst.gty_subst subst gty2 in
  match gty1, gty2 with
  | GTty ty1, GTty ty2 ->
    add_local (env, subst) (x1,ty1) (x2,ty2)

  | GTmodty (p1, r1) , GTmodty(p2, r2) ->
    ensure (ModTy.mod_type_equiv env p1 p2 && NormMp.equal_restr env r1 r2);
    Mod.bind_local x1 p1 r1 env,
    if id_equal x1 x2 then subst
    else Fsubst.f_bind_mod subst x2 (EcPath.mident x1)

  | GTmem   me1, GTmem me2  ->
    check_memtype env me1 me2;
    env,
    if id_equal x1 x2 then subst
    else Fsubst.f_bind_mem subst x2 x1
  | _, _ -> raise NotConv


let check_bindings env subst bd1 bd2 =
    List.fold_left2 check_binding (env,subst) bd1 bd2

(* -------------------------------------------------------------------- *)
let check_alpha_eq hyps f1 f2 =
  let env = LDecl.toenv hyps in
  let exn = IncompatibleForm (env, (f1, f2)) in
  let error () = raise exn in
  let ensure t = if not t then error () in

  let check_local subst id1 f2 id2 =
    match (Mid.find_def f2 id2 subst.fs_loc).f_node with
    | Flocal id2 -> ensure (EcIdent.id_equal id1 id2)
    | _ -> assert false in

  let check_mem subst m1 m2 =
    let m2 = Mid.find_def m2 m2 subst.fs_mem in
    ensure (EcIdent.id_equal m1 m2) in

  let check_pv env subst pv1 pv2 =
    let pv2 = pv_subst (EcPath.x_substm subst.fs_sty.ts_p subst.fs_mp) pv2 in
    ensure (EqTest.for_pv env pv1 pv2) in

  let check_mp env subst mp1 mp2 =
    let mp2 = EcPath.m_subst subst.fs_sty.ts_p subst.fs_mp mp2 in
    ensure (EqTest.for_mp env mp1 mp2) in

  let check_xp env subst xp1 xp2 =
    let xp2 = EcPath.x_substm subst.fs_sty.ts_p subst.fs_mp xp2 in
    ensure (EqTest.for_xp env xp1 xp2) in

  let check_s env s s1 s2 =
    let es = e_subst_init s.fs_freshen s.fs_sty.ts_p
                          s.fs_ty Mp.empty s.fs_mp s.fs_esloc in
    let s2 = EcModules.s_subst es s2 in
    ensure (EqTest.for_stmt env s1 s2) in

  let rec aux env subst f1 f2 =
    if Fsubst.is_subst_id subst && f_equal f1 f2 then ()
    else match f1.f_node, f2.f_node with

    | Fquant(q1,bd1,f1'), Fquant(q2,bd2,f2') when
        q1 = q2 && List.length bd1 = List.length bd2 ->
      let env, subst = check_bindings env subst bd1 bd2 in
      aux env subst f1' f2'

    | Fif(a1,b1,c1), Fif(a2,b2,c2) ->
      aux env subst a1 a2; aux env subst b1 b2; aux env subst c1 c2

    | Fmatch(f1,bs1,ty1), Fmatch(f2,bs2,ty2) ->
      if List.length bs1 <> List.length bs2 then
        error ();
      aux env subst f1 f2;
      ensure (EqTest.for_type env ty1 ty2);
      List.iter2 (aux env subst) bs1 bs2

    | Flet(p1,f1',g1), Flet(p2,f2',g2) ->
      aux env subst f1' f2';
      let (env,subst) = check_lpattern env subst p1 p2 in
      aux env subst g1 g2

    | Fint i1, Fint i2 when EcBigInt.equal i1 i2 -> ()

    | Flocal id1, Flocal id2 -> check_local subst id1 f2 id2

    | Fpvar(p1,m1), Fpvar(p2,m2) ->
      check_mem subst m1 m2;
      check_pv env subst p1 p2

    | Fglob(p1,m1), Fglob(p2,m2) ->
      check_mem subst m1 m2;
      check_mp env subst p1 p2

    | Fop(p1, ty1), Fop(p2, ty2) when EcPath.p_equal p1 p2 ->
      List.iter2 (check_ty env subst) ty1 ty2

    | Fapp(f1',args1), Fapp(f2',args2) when
        List.length args1 = List.length args2 ->
      aux env subst f1' f2';
      List.iter2 (aux env subst) args1 args2

    | Ftuple args1, Ftuple args2 when List.length args1 = List.length args2 ->
      List.iter2 (aux env subst) args1 args2

    | Fproj(f1,i1), Fproj(f2,i2) when i1 = i2 ->
      aux env subst f1 f2

    | FhoareF hf1, FhoareF hf2 ->
      check_xp env subst hf1.hf_f hf2.hf_f;
      aux env subst hf1.hf_pr hf2.hf_pr;
      aux env subst hf1.hf_po hf2.hf_po

    | FhoareS hs1, FhoareS hs2 ->
      check_s env subst hs1.hs_s hs2.hs_s;
      (* FIXME should check the memenv *)
      aux env subst hs1.hs_pr hs2.hs_pr;
      aux env subst hs1.hs_po hs2.hs_po

    | FbdHoareF hf1, FbdHoareF hf2 ->
      ensure (hf1.bhf_cmp = hf2.bhf_cmp);
      check_xp env subst hf1.bhf_f hf2.bhf_f;
      aux env subst hf1.bhf_pr hf2.bhf_pr;
      aux env subst hf1.bhf_po hf2.bhf_po;
      aux env subst hf1.bhf_bd hf2.bhf_bd

    | FbdHoareS hs1, FbdHoareS hs2 ->
      ensure (hs1.bhs_cmp = hs2.bhs_cmp);
      check_s env subst hs1.bhs_s hs2.bhs_s;
      (* FIXME should check the memenv *)
      aux env subst hs1.bhs_pr hs2.bhs_pr;
      aux env subst hs1.bhs_po hs2.bhs_po;
      aux env subst hs1.bhs_bd hs2.bhs_bd

    | FequivF ef1, FequivF ef2 ->
      check_xp env subst ef1.ef_fl ef2.ef_fl;
      check_xp env subst ef1.ef_fr ef2.ef_fr;
      aux env subst ef1.ef_pr ef2.ef_pr;
      aux env subst ef1.ef_po ef2.ef_po

    | FequivS es1, FequivS es2 ->
      check_s env subst es1.es_sl es2.es_sl;
      check_s env subst es1.es_sr es2.es_sr;
      (* FIXME should check the memenv *)
      aux env subst es1.es_pr es2.es_pr;
      aux env subst es1.es_po es2.es_po

    | FeagerF eg1, FeagerF eg2 ->
      check_xp env subst eg1.eg_fl eg2.eg_fl;
      check_xp env subst eg1.eg_fr eg2.eg_fr;
      aux env subst eg1.eg_pr eg2.eg_pr;
      aux env subst eg1.eg_po eg2.eg_po;
      check_s env subst eg1.eg_sl eg2.eg_sl;
      check_s env subst eg1.eg_sr eg2.eg_sr

    | Fpr pr1, Fpr pr2 ->
      check_mem subst pr1.pr_mem pr2.pr_mem;
      check_xp env subst pr1.pr_fun pr2.pr_fun;
      aux env subst pr1.pr_args pr2.pr_args;
      aux env subst pr1.pr_event pr2.pr_event

    | _, _ -> error ()

  in
  try aux env Fsubst.f_subst_id f1 f2
  with NotConv -> raise exn

(* -------------------------------------------------------------------- *)
let is_alpha_eq hyps f1 f2 =
  try check_alpha_eq hyps f1 f2; true
  with IncompatibleForm _ -> false

(* -------------------------------------------------------------------- *)
type reduction_info = {
  beta    : bool;
  delta_p : (path  -> deltap); (* reduce operators *)
  delta_h : (ident -> bool);   (* reduce local definitions *)
  zeta    : bool;
  iota    : bool;
  eta     : bool;
  logic   : rlogic_info;
  modpath : bool;
  user    : bool;
}

and deltap      = [`Yes | `No | `Force]
and rlogic_info = [`Full | `ProductCompat] option

(* -------------------------------------------------------------------- *)
let full_red = {
  beta    = true;
  delta_p = (fun _ -> `Yes);
  delta_h = EcUtils.predT;
  zeta    = true;
  iota    = true;
  eta     = true;
  logic   = Some `Full;
  modpath = true;
  user    = true;
}

let no_red = {
  beta    = false;
  delta_p = (fun _ -> `No);
  delta_h = EcUtils.pred0;
  zeta    = false;
  iota    = false;
  eta     = false;
  logic   = None;
  modpath = false;
  user    = false;
}

let beta_red     = { no_red with beta = true; }
let betaiota_red = { no_red with beta = true; iota = true; }

let nodelta =
  { full_red with
      delta_h = EcUtils.pred0;
      delta_p = (fun _ -> `No); }

let delta = { no_red with delta_p = (fun _ -> `Yes); }

let full_compat = { full_red with logic = Some `ProductCompat; }

(* -------------------------------------------------------------------- *)
type not_reducible = NoHead | NeedSubTerm

exception NotRed of not_reducible

let nohead = NotRed NoHead
let needsubterm = NotRed NeedSubTerm

(* -------------------------------------------------------------------- *)
let reduce_local ri hyps x  =
  if   ri.delta_h x
  then try LDecl.unfold x hyps with NotReducible -> raise nohead
  else raise nohead

let reduce_op ri env p tys =
  if ri.delta_p p <> `No then
    try
      Op.reduce ~force:(ri.delta_p p = `Force) env p tys
    with NotReducible -> raise nohead
  else raise nohead

let is_record env f =
  match EcFol.destr_app f with
  | { f_node = Fop (p, _) }, _ -> EcEnv.Op.is_record_ctor env p
  | _ -> false

(* -------------------------------------------------------------------- *)
let can_eta x (f, args) =
  match List.rev args with
  | { f_node = Flocal y } :: args ->
      let check v = not (Mid.mem x v.f_fv) in
      id_equal x y && List.for_all check (f :: args)
  | _ -> false

let eta_expand bd f ty =
  let args =
    List.map (fun (x,gty) ->
        match gty with
        | GTty ty -> f_local x ty
        | _      -> assert false) bd in
  (f_app f args ty)

(* -------------------------------------------------------------------- *)
let reduce_user_gen simplify ri env hyps f =
  if not ri.user then raise nohead;

  let p =
    match f_node (fst (destr_app f)) with
    | Fop (p, _) -> `Path p
    | Ftuple _   -> `Tuple
    | _ -> raise nohead in

  let rules = EcEnv.Reduction.get p env in

  if rules = [] then raise nohead;

  let module R = EcTheory in

  oget ~exn:needsubterm (List.Exceptionless.find_map (fun rule ->

    let ue  = EcUnify.UniEnv.create None in
    let tvi = EcUnify.UniEnv.opentvi ue rule.R.rl_tyd None in
    let pv  = ref Mid.empty in

    try
      let rec doit f ptn =
        match destr_app f, ptn with
        | ({ f_node = Fop (p, tys) }, args), R.Rule (`Op (p', tys'), args')
              when EcPath.p_equal p p' && List.length args = List.length args' ->

          let tys' = List.map (EcTypes.Tvar.subst tvi) tys' in

          begin
            try  List.iter2 (EcUnify.unify env ue) tys tys'
            with EcUnify.UnificationFailure _ -> raise NotReducible end;

          List.iter2 doit args args'

        | ({ f_node = Ftuple args} , []), R.Rule (`Tuple, args')
            when List.length args = List.length args' ->

          List.iter2 doit args args'

        | ({ f_node = Fint i }, []), R.Int j when EcBigInt.equal i j ->
            ()

        | _, R.Var x -> begin
            match Mid.find_opt x !pv with
            | None    -> pv := Mid.add x f !pv
            | Some f' ->
              (* FIXME : check_alpha_equal ri hyps f f' *)
              check_alpha_eq hyps f f'
          end

        | _ -> raise NotReducible in

      doit f rule.R.rl_ptn;

      if not (EcUnify.UniEnv.closed ue) then
        raise NotReducible;

      let subst f =
        let tysubst = { ty_subst_id with ts_u = EcUnify.UniEnv.assubst ue } in
        let subst   = Fsubst.f_subst_init ~sty:tysubst () in
        let subst   = Mid.fold (fun x f s -> Fsubst.f_bind_local s x f) !pv subst in
        Fsubst.f_subst subst (Fsubst.subst_tvar tvi f)
      in

      List.iter (fun cond ->
        if not (f_equal (simplify (subst cond)) f_true) then
          raise NotReducible)
        rule.R.rl_cond;

      Some (subst rule.R.rl_tg)

    with NotReducible -> None)
  rules)

(* -------------------------------------------------------------------- *)
let check_reduced hyps exn f f' =
  if is_alpha_eq hyps f f' then raise exn else f'

(* -------------------------------------------------------------------- *)
let reduce_quant ri _env hyps f =
  match f.f_node with
  | Fquant (Lforall as t, b, f1)
  | Fquant (Lexists as t, b, f1) when ri.logic = Some `Full ->
    let f' = match t with
      | Lforall -> f_forall_simpl b f1
      | Lexists -> f_exists_simpl b f1
      | Llambda -> assert false in
    check_reduced hyps needsubterm f f'
  | _ -> raise nohead

(* -------------------------------------------------------------------- *)
let reduce_logic ri env hyps f p args =
  let pcompat =
    match ri.logic with
    | Some `Full -> true
    | Some `ProductCompat -> false
    | None -> raise nohead
  in

  let f' =
    match op_kind p, args with
    | Some (`Imp), [f1;f2] when pcompat -> f_imp_simpl f1 f2
    | Some (`Iff), [f1;f2] when pcompat -> f_iff_simpl f1 f2

    | Some (`Not)      , [f1]    -> f_not_simpl f1
    | Some (`And `Asym), [f1;f2] -> f_anda_simpl f1 f2
    | Some (`Or  `Asym), [f1;f2] -> f_ora_simpl f1 f2
    | Some (`And `Sym ), [f1;f2] -> f_and_simpl f1 f2
    | Some (`Or  `Sym ), [f1;f2] -> f_or_simpl f1 f2
    | Some (`Int_le   ), [f1;f2] -> f_int_le_simpl f1 f2
    | Some (`Int_lt   ), [f1;f2] -> f_int_lt_simpl f1 f2
    | Some (`Real_le  ), [f1;f2] -> f_real_le_simpl f1 f2
    | Some (`Real_lt  ), [f1;f2] -> f_real_lt_simpl f1 f2
    | Some (`Int_add  ), [f1;f2] -> f_int_add_simpl f1 f2
    | Some (`Int_opp  ), [f]     -> f_int_opp_simpl f
    | Some (`Int_mul  ), [f1;f2] -> f_int_mul_simpl f1 f2
    | Some (`Int_edivz), [f1;f2] -> f_int_edivz_simpl f1 f2
    | Some (`Real_add ), [f1;f2] -> f_real_add_simpl f1 f2
    | Some (`Real_opp ), [f]     -> f_real_opp_simpl f
    | Some (`Real_mul ), [f1;f2] -> f_real_mul_simpl f1 f2
    | Some (`Real_inv ), [f]     -> f_real_inv_simpl f
    | Some (`Eq       ), [f1;f2] ->
      begin
        match fst_map f_node (destr_app f1), fst_map f_node (destr_app f2) with
        | (Fop (p1, _), args1), (Fop (p2, _), args2)
            when EcEnv.Op.is_dtype_ctor env p1
                 && EcEnv.Op.is_dtype_ctor env p2 ->

          let idx p =
            let idx = EcEnv.Op.by_path p env in
            snd (EcDecl.operator_as_ctor idx)
          in
          if   idx p1 <> idx p2
          then f_false
          else f_ands (List.map2 f_eq args1 args2)

        | (_, []), (_, [])
            when EqTest.for_type env f1.f_ty EcTypes.tunit
                 && EqTest.for_type env f2.f_ty EcTypes.tunit ->

          f_true

        | _ ->
          if   f_equal f1 f2 || is_alpha_eq hyps f1 f2
          then f_true
          else f_eq_simpl f1 f2
      end

    | _ -> raise nohead
  in
  check_reduced hyps needsubterm f f'

(* -------------------------------------------------------------------- *)
let reduce_delta ri env _hyps f =
  match f.f_node with
  | Fop (p, tys) when ri.delta_p p <> `No ->
      reduce_op ri env p tys

  | Fapp ({ f_node = Fop (p, tys) }, args) when ri.delta_p p <> `No ->
      let op = reduce_op ri env p tys in
      f_app_simpl op args f.f_ty

  | _ -> raise nohead

(* -------------------------------------------------------------------- *)
(* Perform one step of head reduction                                   *)
let reduce_head simplify ri env hyps f =
  match f.f_node with
    (* β-reduction *)
  | Fapp ({ f_node = Fquant (Llambda, _, _)}, _) when ri.beta ->
      f_betared f

    (* ζ-reduction *)
  | Flocal x -> reduce_local ri hyps x

    (* ζ-reduction *)
  | Fapp ({ f_node = Flocal x }, args) ->
      f_app_simpl (reduce_local ri hyps x) args f.f_ty

    (* ζ-reduction *)
  | Flet (LSymbol(x,_), e1, e2) when ri.zeta ->
      let s = Fsubst.f_bind_local Fsubst.f_subst_id x e1 in
      Fsubst.f_subst s e2

    (* ι-reduction (let-tuple) *)
  | Flet (LTuple ids, e1, e2) when ri.iota ->
    if is_tuple e1 then
      let es = destr_tuple e1 in
      let s =
        List.fold_left2
          (fun s (x,_) e -> Fsubst.f_bind_local s x e)
          Fsubst.f_subst_id ids es
      in
        Fsubst.f_subst s e2
    else raise needsubterm

    (* ι-reduction (let-records) *)
  | Flet (LRecord (_, ids), f1, f2) when ri.iota ->
    if is_record env f1 then
      let args  = snd (EcFol.destr_app f1) in
      let subst =
        List.fold_left2 (fun subst (x, _) e ->
          match x with
          | None   -> subst
          | Some x -> Fsubst.f_bind_local subst x e)
          Fsubst.f_subst_id ids args
      in
        Fsubst.f_subst subst f2
    else raise nohead

    (* ι-reduction (records projection) *)
  | Fapp ({ f_node = Fop (p, _); }, args)
      when ri.iota && EcEnv.Op.is_projection env p ->
      begin match args with
      | mk :: args ->
        begin match mk.f_node with
        | Fapp ({ f_node = Fop (mkp, _) }, mkargs) ->
          if not (EcEnv.Op.is_record_ctor env mkp) then raise nohead;
          let v = oget (EcEnv.Op.by_path_opt p env) in
          let v = proj3_2 (EcDecl.operator_as_proj v) in
          let v = List.nth mkargs v in
          f_app v args f.f_ty

        | _ -> raise needsubterm
        end
      | _ -> raise nohead
      end

    (* ι-reduction (tuples projection) *)
  | Fproj(f1, i) when ri.iota ->
    check_reduced hyps needsubterm f (f_proj_simpl f1 i f.f_ty)

    (* ι-reduction (if-then-else) *)
  | Fif (f1, f2, f3) when ri.iota ->
    check_reduced hyps needsubterm f (f_if_simpl f1 f2 f3)

    (* ι-reduction (if-then-else) *)
  | Fmatch (c, bs, ty) when ri.iota -> begin
      let op, args = destr_app c in

        match op.f_node with
        | Fop (p, _) when EcEnv.Op.is_dtype_ctor env p ->
            let idx = EcEnv.Op.by_path p env in
            let idx = snd (EcDecl.operator_as_ctor idx) in
            let br  = oget (List.nth_opt bs idx) in
            f_app br args ty

        | _ -> raise needsubterm
    end

    (* ι-reduction (match-fix) *)
  | Fapp ({ f_node = Fop (p, tys); }, fargs)
      when ri.iota && EcEnv.Op.is_fix_def env p ->

      let op  = oget (EcEnv.Op.by_path_opt p env) in
      let fix = EcDecl.operator_as_fix op in

      if List.length fargs < snd (fix.EcDecl.opf_struct) then
        raise nohead;

      let fargs, eargs = List.split_at (snd (fix.EcDecl.opf_struct)) fargs in

      let args  = Array.of_list fargs in
      let pargs = List.fold_left (fun (opb, acc) v ->
             let v = args.(v) in
              match fst_map (fun x -> x.f_node) (EcFol.destr_app v) with
              | (Fop (p, _), cargs) when EcEnv.Op.is_dtype_ctor env p -> begin
                  let idx = EcEnv.Op.by_path p env in
                  let idx = snd (EcDecl.operator_as_ctor idx) in
                  match opb with
                  | EcDecl.OPB_Leaf   _  -> assert false
                  | EcDecl.OPB_Branch bs ->
                    ((Parray.get bs idx).EcDecl.opb_sub, cargs :: acc)
                end
              | _ -> raise needsubterm)
            (fix.EcDecl.opf_branches, []) (fst fix.EcDecl.opf_struct)
      in

      let pargs, (bds, body) =
        match pargs with
        | EcDecl.OPB_Leaf (bds, body), cargs -> (List.rev cargs, (bds, body))
        | _ -> assert false
      in

      let subst =
        List.fold_left2
          (fun subst (x, _) fa -> Fsubst.f_bind_local subst x fa)
          Fsubst.f_subst_id fix.EcDecl.opf_args fargs in

      let subst =
        List.fold_left2
          (fun subst bds cargs ->
            List.fold_left2
              (fun subst (x, _) fa -> Fsubst.f_bind_local subst x fa)
              subst bds cargs)
          subst bds pargs in

      let body = EcFol.form_of_expr EcFol.mhr body in
      let body =
        EcFol.Fsubst.subst_tvar
          (EcTypes.Tvar.init (List.map fst op.EcDecl.op_tparams) tys) body in

      f_app (Fsubst.f_subst subst body) eargs f.f_ty

    (* μ-reduction *)
  | Fglob (mp, m) when ri.modpath ->
    let f' = NormMp.norm_glob env m mp in
    if f_equal f f' then raise nohead else f'

    (* μ-reduction *)
  | Fpvar (pv, m) when ri.modpath ->
    let f' = f_pvar (NormMp.norm_pvar env pv) f.f_ty m in
    if f_equal f f' then raise nohead else f'

    (* η-reduction *)
  | Fquant (Llambda, [x, GTty _], { f_node = Fapp (fn, args) })
      when ri.eta && can_eta x (fn, args)
    -> f_app fn (List.take (List.length args - 1) args) f.f_ty

  | Fop _ -> reduce_delta ri env hyps f

  | Fapp({ f_node = Fop(p,_); }, args) -> begin
      try  reduce_logic ri env hyps f p args
      with NotRed kind1 ->
        try  reduce_user_gen simplify ri env hyps f
        with NotRed kind2 ->
          if kind1 = NoHead && kind2 = NoHead then reduce_delta ri env hyps f
          else raise needsubterm
    end

  | Fapp(_, _) -> raise needsubterm

  | Fquant((Lforall | Lexists), _, _) ->
    reduce_quant ri env hyps f

  | _ -> raise nohead

let rec eta_norm f =
  match f.f_node with
  | Fquant (Llambda, [x, GTty _], { f_node = Fapp (fn, args) })
      when can_eta x (fn, args)
    -> eta_norm (f_app fn (List.take (List.length args - 1) args) f.f_ty)
  | _ -> f

(* -------------------------------------------------------------------- *)
type reduced =
  | Red of bool * form (* bool true => at least on head reduction has been done *)
  | Norm               (* The term is in weak_head normal from (no reduction under lambda *)
  | Unknown

module RedTbl : sig
  type t

  val init        : unit -> t
  val get         : t -> form -> reduced
  val set_reduced : t -> form -> form -> unit
  val set_sub     : t -> form -> form -> unit
  val set_norm    : t -> form -> unit
end = struct
  type t = reduced Hf.t

  let init () =
    Hf.create 1023

  let rec get redtbl f =
    match Hf.find redtbl f with
    | Red (h1, f1) as r -> begin
        match get redtbl f1 with
        | Red (h2,f2) as r1 ->
          let r1 = if h1 = h2 then r1 else Red (h1 || h2, f2) in
          Hf.replace redtbl f r1; r1
        | Norm | Unknown -> r
      end
    | (Norm | Unknown) as r -> r
    | exception Not_found -> Unknown

  let set_reduced redtbl f f' = Hf.replace redtbl f (Red (true, f'))
  let set_sub     redtbl f f' = Hf.replace redtbl f (Red (false, f'))
  let set_norm    redtbl f    = Hf.replace redtbl f Norm
end

type redtbl = RedTbl.t

(* -------------------------------------------------------------------- *)
type redinfo = {
  ri     : reduction_info;
  redtbl : redtbl;
  hyps   : LDecl.hyps;
}

(* -------------------------------------------------------------------- *)
let init_redinfo ri hyps =
  ({ ri; hyps; redtbl = RedTbl.init (); }, LDecl.toenv hyps)

(* -------------------------------------------------------------------- *)
let rec reduce_head_top (ri:redinfo) env ~onhead f =
  match RedTbl.get ri.redtbl f with
  | Norm    -> raise nohead
  | Red (h,f')  ->
    if h || not onhead then f'
    else reduce_head_top_force ri env onhead f'
  | Unknown -> reduce_head_top_force ri env onhead f

and reduce_head_top_force ri env onhead f =
  match reduce_head (whnf ri env) ri.ri env ri.hyps f with
  | f' ->
    RedTbl.set_reduced ri.redtbl f f'; f'

  | exception (NotRed NoHead) when is_tuple f && not onhead -> begin
      match reduce_head_sub ri env f with
      | f' -> f'
      | exception (NotRed _) -> RedTbl.set_norm ri.redtbl f; raise nohead
    end

  | exception (NotRed NeedSubTerm) -> begin
    match reduce_head_sub ri env f with
    | f ->
      if onhead then reduce_head_top ri env ~onhead f else f
    | exception (NotRed _) ->
      try reduce_delta ri.ri env ri.hyps f
      with NotRed _ -> RedTbl.set_norm ri.redtbl f; raise nohead
  end

and reduce_head_sub ri env f =
  let f' =
    match f.f_node with
    | Fapp({f_node = Fop _} as f1, args) ->
      f_app f1 (reduce_head_args ri env args) f.f_ty

    | Fapp (f1, args) -> begin
        match reduce_head_args ri env (f1::args) with
        | f1::args -> f_app f1 args f.f_ty
        | []       -> assert false
      end

    | Fquant ((Lforall | Lexists) as t, b, f1) ->
      let env = Mod.add_mod_binding b env in
      f_quant t b (reduce_head_top ri env ~onhead:false f1)

    | Flet(lp, f1, f2) ->
      curry (f_let lp) (as_seq2 (reduce_head_args ri env [f1;f2]))

    | Fproj(f1,i) ->
      f_proj (reduce_head_top ri env ~onhead:false f1) i f.f_ty

    | Fif (f1, f2, f3) ->
      curry3 f_if (as_seq3 (reduce_head_args ri env [f1; f2; f3]))

    | Fmatch (c, bs, tys) ->
      let c, bs =
        match reduce_head_args ri env (c :: bs) with
        | [] -> assert false
        | c :: bs -> (c, bs)
      in f_match c bs tys

    | Ftuple args ->
      f_tuple (reduce_head_args ri env args)

    | _ -> assert false

  in RedTbl.set_sub ri.redtbl f f'; f'

and reduce_head_args ri env args =
  match args with
  | [] -> raise nohead
  | a :: args ->
    try  reduce_head_top ri env ~onhead:false a :: args
    with NotRed _ -> a :: reduce_head_args ri env args

(* Performs head reduction when possible *)
and whnf ri env f =
  match reduce_head_top ri env ~onhead:true f with
  | f -> whnf ri env f
  | exception (NotRed _) -> f

(* -------------------------------------------------------------------- *)
let rec simplify ri env f =
  let f = whnf ri env f in
  match f.f_node with
  | FhoareF hf when ri.ri.modpath ->
      let hf_f = EcEnv.NormMp.norm_xfun env hf.hf_f in
      f_map (fun ty -> ty) (simplify ri env) (f_hoareF_r { hf with hf_f })

  | FbdHoareF hf when ri.ri.modpath ->
      let bhf_f = EcEnv.NormMp.norm_xfun env hf.bhf_f in
      f_map (fun ty -> ty) (simplify ri env) (f_bdHoareF_r { hf with bhf_f })

  | FequivF ef when ri.ri.modpath ->
      let ef_fl = EcEnv.NormMp.norm_xfun env ef.ef_fl in
      let ef_fr = EcEnv.NormMp.norm_xfun env ef.ef_fr in
      f_map (fun ty -> ty) (simplify ri env) (f_equivF_r { ef with ef_fl; ef_fr; })

  | FeagerF eg when ri.ri.modpath ->
      let eg_fl = EcEnv.NormMp.norm_xfun env eg.eg_fl in
      let eg_fr = EcEnv.NormMp.norm_xfun env eg.eg_fr in
      f_map (fun ty -> ty) (simplify ri env) (f_eagerF_r { eg with eg_fl ; eg_fr; })

  | Fpr pr when ri.ri.modpath ->
      let pr_fun = EcEnv.NormMp.norm_xfun env pr.pr_fun in
      f_map (fun ty -> ty) (simplify ri env) (f_pr_r { pr with pr_fun })

  | Fquant (q, bd, f) ->
    let env = Mod.add_mod_binding bd env in
    f_quant q bd (simplify ri env f)

  | _ ->
    f_map (fun ty -> ty) (simplify ri env) f

let simplify ri hyps f =
  let ri, env = init_redinfo ri hyps in
  simplify ri env f

(* ----------------------------------------------------------------- *)
(* Checking convertibility                                           *)

let check_bindings_conv env q bd1 bd2 f1 f2 =
  let rec aux es bd bd1 bd2 =
    match bd1, bd2 with
    | b1::bd1', b2::bd2' ->
      begin match check_binding es b1 b2 with
      | es -> aux es (b1::bd) bd1' bd2'
      | exception NotConv -> es, bd, bd1, bd2
      end
    | _, _ -> es, bd, bd1, bd2 in
  let (env, subst), bd, bd1, bd2 = aux (env, Fsubst.f_subst_id) [] bd1 bd2 in
  env, bd, f_quant q bd1 f1, f_quant q bd2 (Fsubst.f_subst subst f2)

let check_memenv env (x1,mt1) (x2,mt2) =
  EcMemory.mem_equal x1 x2 &&
    try check_memtype env mt1 mt2; true with NotConv -> false

(* -------------------------------------------------------------------- *)
type head_sub =
  | Zquant of quantif * bindings (* in reversed order *)
  | Zif
  | Zmatch of EcTypes.ty
  | Zlet   of lpattern
  | Zapp
  | Ztuple
  | Zproj  of int
  | Zhl    of form (* program logic predicates *)

type stk_elem = {
    se_h      : head_sub;
    se_common : form list;
    se_args1  : form list;
    se_args2  : form list;
    se_ty     : ty;
  }

type stk = stk_elem list

let zpush se_h se_common se_args1 se_args2 se_ty stk =
  { se_h; se_common; se_args1; se_args2; se_ty} :: stk

(* FIXME normalize zquant *)

let zquant q bd ty stk = zpush (Zquant (q, bd)) [] [] [] ty stk
let zif args1 args2 ty stk = zpush Zif [] args1 args2 ty stk
let zmatch bsty args1 args2 ty stk = zpush (Zmatch bsty) [] args1 args2 ty stk
let zlet lp f1 f2 stk = zpush (Zlet lp) [] [f1] [f2] f1.f_ty stk

let zapp args1 args2 ty stk =
  match stk with
  | se::stk when se.se_h = Zapp && se.se_common = [] ->
    zpush Zapp [] (args1 @ se.se_args1) (args2 @ se.se_args2) se.se_ty stk
  | _ -> zpush Zapp [] args1 args2 ty stk

let ztuple args1 args2 ty stk = zpush Ztuple [] args1 args2 ty stk
let zproj i ty stk = zpush (Zproj i) [] [] [] ty stk
let zhl f fs1 fs2 stk = zpush (Zhl f) [] fs1 fs2 f.f_ty stk

let zpop ri side f hd =
  let args =
    match side with
    | `Left  -> hd.se_args1
    | `Right -> hd.se_args2 in
  let args = List.rev_append hd.se_common (f::args) in
  match hd.se_h, args with
  | Zquant(Llambda,bd), [f] when ri.ri.eta -> eta_norm (f_lambda bd f)

  | Zquant(q,bd), [f]  -> f_quant q bd f
  | Zif, [f1;f2;f3]    -> f_if f1 f2 f3
  | Zmatch ty, c :: bs -> f_match c bs ty
  | Zlet lp, [f1;f2]   -> f_let lp f1 f2
  | Zapp, f1::args     -> f_app f1 args hd.se_ty
  | Ztuple, args       -> f_tuple args
  | Zproj i, [f1]      -> f_proj f1 i hd.se_ty
  | Zhl {f_node = FhoareF hf}, [pr;po] ->
    f_hoareF_r {hf with hf_pr = pr; hf_po = po }
  | Zhl {f_node = FhoareS hs}, [pr;po] ->
    f_hoareS_r {hs with hs_pr = pr; hs_po = po }
  | Zhl {f_node = FbdHoareF hf}, [pr;po;bd] ->
    f_bdHoareF_r {hf with bhf_pr = pr; bhf_po = po; bhf_bd = bd}
  | Zhl {f_node = FbdHoareS hs}, [pr;po;bd] ->
    f_bdHoareS_r {hs with bhs_pr = pr; bhs_po = po; bhs_bd = bd}
  | Zhl {f_node = FequivF hf}, [pr;po] ->
    f_equivF_r {hf with ef_pr = pr; ef_po = po }
  | Zhl {f_node = FequivS hs}, [pr;po] ->
    f_equivS_r {hs with es_pr = pr; es_po = po }
  | Zhl {f_node = FeagerF hs}, [pr;po] ->
    f_eagerF_r {hs with eg_pr = pr; eg_po = po }
  | Zhl {f_node = Fpr hs}, [a;ev] ->
    f_pr_r {hs with pr_args = a; pr_event = ev }
  | _, _ -> assert false

(* -------------------------------------------------------------------- *)
let rec conv ri env f1 f2 stk =
  if f_equal f1 f2 then conv_next ri env f1 stk else
  match f1.f_node, f2.f_node with
  | Fquant (q1, bd1, f1'), Fquant(q2,bd2,f2') ->
    if q1 <> q2 then force_head_sub ri env f1 f2 stk
    else
      let env, bd, f1', f2' = check_bindings_conv env q1 bd1 bd2 f1' f2' in
      if bd = [] then force_head ri env f1 f2 stk
      else conv ri env f1' f2' (zquant q1 (List.rev bd) f1.f_ty stk)

  | Fquant(Llambda, bd, f), _ -> begin
    match stk with
    | se::stk when se.se_h = Zapp && se.se_common = [] && ri.ri.beta ->
      let f1 = f_betared (zpop ri `Left  f1 se) in
      let f2 = zpop ri `Right f2 se in
      conv ri env f1 f2 stk
    | _ ->
      if ri.ri.eta then
        conv ri env f (eta_expand bd f2 f.f_ty) (zquant Llambda bd f1.f_ty stk)
      else force_head ri env f1 f2 stk
    end

  | _, Fquant(Llambda, bd, f) -> begin
    match stk with
    | se::stk when se.se_h = Zapp && se.se_common = [] && ri.ri.beta ->
      let f1 = zpop ri `Left  f1 se in
      let f2 = f_betared (zpop ri `Right f2 se) in
      conv ri env f1 f2 stk
    | _ ->
      if ri.ri.eta then
        conv ri env (eta_expand bd f1 f.f_ty) f (zquant Llambda bd f2.f_ty stk)
      else force_head ri env f1 f2 stk
    end

  | Fif(f11, f12, f13), Fif(f21,f22,f23) ->
    conv ri env f11 f21 (zif [f12;f13] [f22;f23] f1.f_ty stk)

  | Fmatch(c1,bs1,ty1), Fmatch(c2,bs2,ty2) when
          List.length bs1 = List.length bs2
       && EqTest.for_type env ty1 ty2
    -> conv ri env c1 c2 (zmatch ty1 bs1 bs2 f1.f_ty stk)

  | Flet(lp1,f11,f12), Flet(lp2,f21,f22) -> begin
    match check_lpattern env Fsubst.f_subst_id lp1 lp2 with
    | env, subst ->
      let f21, f22 = Fsubst.f_subst subst f21, Fsubst.f_subst subst f22 in
      conv ri env f11 f21 (zlet lp1 f12 f22 stk)
    | exception NotConv -> force_head ri env f1 f2 stk
    end

  | Fop(p1, ty1), Fop(p2,ty2)
      when EcPath.p_equal p1 p2 && List.all2 (EqTest.for_type env) ty1 ty2 ->
    conv_next ri env f1 stk

  | Fapp(f1', args1), Fapp(f2', args2)
      when EqTest.for_type env f1'.f_ty f2'.f_ty
        && List.length args1 = List.length args2 -> begin
    (* So that we do not unfold operators *)
    match f1'.f_node, f2'.f_node with
    | Fop(p1, _), Fop(p2, _) when EcPath.p_equal p1 p2 ->
      conv_next ri env f1' (zapp args1 args2 f1.f_ty stk)
    | _, _ ->
      conv ri env f1' f2' (zapp args1 args2 f1.f_ty stk)
    end

  | Ftuple [], Ftuple [] ->
    conv_next ri env f1 stk

  | Ftuple (f1'::args1), Ftuple(f2'::args2)
      when List.length args1 = List.length args2 ->
    conv ri env f1' f2' (ztuple args1 args2 f1.f_ty stk)

  | Fproj(f1', i1), Fproj(f2',i2) when i1 = i2 ->
    conv ri env f1' f2' (zproj i1 f1.f_ty stk)

  | FhoareF hf1, FhoareF hf2 when EqTest.for_xp env hf1.hf_f hf2.hf_f ->
    conv ri env hf1.hf_pr hf2.hf_pr (zhl f1 [hf1.hf_po] [hf2.hf_po] stk)

  | FhoareS hs1, FhoareS hs2
      when EqTest.for_stmt env hs1.hs_s hs2.hs_s ->
    conv ri env hs1.hs_pr hs2.hs_pr (zhl f1 [hs1.hs_po] [hs2.hs_po] stk)

  | FbdHoareF hf1, FbdHoareF hf2
      when EqTest.for_xp env hf1.bhf_f hf2.bhf_f && hf1.bhf_cmp = hf2.bhf_cmp  ->
    conv ri env hf1.bhf_pr hf2.bhf_pr
      (zhl f1 [hf1.bhf_po;hf1.bhf_bd] [hf2.bhf_po; hf2.bhf_bd] stk)

  | FbdHoareS hs1, FbdHoareS hs2
      when EqTest.for_stmt env hs1.bhs_s hs2.bhs_s
        && hs1.bhs_cmp = hs2.bhs_cmp ->
    conv ri env hs1.bhs_pr hs2.bhs_pr
      (zhl f1 [hs1.bhs_po;hs1.bhs_bd] [hs2.bhs_po; hs2.bhs_bd] stk)

  | FequivF ef1, FequivF ef2
      when EqTest.for_xp env ef1.ef_fl ef2.ef_fl
        && EqTest.for_xp env ef1.ef_fr ef2.ef_fr ->
    conv ri env ef1.ef_pr ef2.ef_pr (zhl f1 [ef1.ef_po] [ef2.ef_po] stk)

  | FequivS es1, FequivS es2
      when EqTest.for_stmt env es1.es_sl es2.es_sl
        && EqTest.for_stmt env es1.es_sr es2.es_sr ->
    conv ri env es1.es_pr es2.es_pr (zhl f1 [es1.es_po] [es2.es_po] stk)

  | FeagerF eg1, FeagerF eg2 ->
    if    EqTest.for_xp env eg1.eg_fl eg2.eg_fl
       && EqTest.for_xp env eg1.eg_fr eg2.eg_fr
       && EqTest.for_stmt env eg1.eg_sl eg2.eg_sl
       && EqTest.for_stmt env eg1.eg_sr eg2.eg_sr then
      conv ri env eg1.eg_pr eg2.eg_pr (zhl f1 [eg1.eg_po] [eg2.eg_po] stk)
    else
      force_head ri env f1 f2 stk

  | Fpr pr1, Fpr pr2 ->
    if EcMemory.mem_equal pr1.pr_mem pr2.pr_mem &&
         EqTest.for_xp env pr1.pr_fun pr2.pr_fun then
      conv ri env pr1.pr_args pr2.pr_args (zhl f1 [pr1.pr_event] [pr2.pr_event] stk)
    else
      force_head ri env f1 f2 stk

  | _, _ -> force_head ri env f1 f2 stk

(* -------------------------------------------------------------------- *)
and conv_next ri env f stk =
  match stk with
  | [] -> true
  | hd::stk ->
    match hd.se_args1, hd.se_args2 with
    | [], [] ->
      let f1 = zpop ri `Left f hd in
      conv_next ri env f1 stk
    | f1::args1, f2::args2 ->
      let hd = { hd with se_common = f::hd.se_common;
                         se_args1  = args1;
                         se_args2  = args2; } in
      conv ri env f1 f2 (hd::stk)
    | _, _ -> assert false

and force_head ri env f1 f2 stk =
  (* FIXME add oracle to decide what to do *)
  let reduce_first side f1 f2 stk =
    let f = if side = `Left then f1 else f2 in
    match stk with
    | se::stk when is_op f && se.se_h = Zapp && se.se_common = [] ->
      let f1 = zpop ri `Left  f1 se in
      let f2 = zpop ri `Right f2 se in
      f1, f2, stk
    | _ -> f1, f2, stk in

  let f1', f2', stk' = reduce_first `Left f1 f2 stk in
  match reduce_head_top ri env ~onhead:true f1' with
  | f1' -> conv ri env f1' f2' stk'
  | exception (NotRed _) ->
    let f1', f2', stk' = reduce_first `Right f1 f2 stk in
    match reduce_head_top ri env ~onhead:true f2' with
    | f2' -> conv ri env f1' f2' stk'
    | exception (NotRed _) ->
      force_head_sub ri env f1 f2 stk

and force_head_sub ri env f1 f2 stk =
  match stk with
  | [] -> false
  | hd::stk ->
    let f1 = zpop ri `Left  f1 hd in
    let f2 = zpop ri `Right f2 hd in
    force_head ri env f1 f2 stk

(* -------------------------------------------------------------------- *)
let reduce_user_gen simplify ri env hyps f =
  try reduce_user_gen simplify ri env hyps f
  with NotRed _ -> raise NotReducible

(* -------------------------------------------------------------------- *)
let is_conv ?(ri = full_red) hyps f1 f2 =
  if f_equal f1 f2 then true
  else
    let ri, env = init_redinfo ri hyps in
    if EqTest.for_type env f1.f_ty f2.f_ty then conv ri env f1 f2 []
    else false

let check_conv ?ri hyps f1 f2 =
  if is_conv ?ri hyps f1 f2 then ()
  else raise (IncompatibleForm ((LDecl.toenv hyps), (f1, f2)))

(* -------------------------------------------------------------------- *)
let h_red ri hyps f =
  try
    let ri, env = init_redinfo ri hyps in
    reduce_head_top ri env ~onhead:true f
  with NotRed _ -> raise NotReducible

let h_red_opt ri hyps f =
  try Some (h_red ri hyps f)
  with NotReducible -> None

(* -------------------------------------------------------------------- *)
type xconv = [`Eq | `AlphaEq | `Conv]

let xconv (mode : xconv) hyps =
  match mode with
  | `Eq      -> f_equal
  | `AlphaEq -> is_alpha_eq hyps
  | `Conv    -> is_conv hyps


(* -------------------------------------------------------------------- *)
module User = struct
  type options = EcTheory.rule_option

  type error =
    | MissingVarInLhs   of EcIdent.t
    | MissingTyVarInLhs of EcIdent.t
    | NotAnEq
    | NotFirstOrder
    | RuleDependsOnMemOrModule
    | HeadedByVar

  exception InvalidUserRule of error

  module R = EcTheory

  type rule = EcEnv.Reduction.rule

  let compile ~opts ~prio (env : EcEnv.env) (p : EcPath.path) =
    let simp =
      if opts.EcTheory.ur_delta then
        let hyps = EcEnv.LDecl.init env [] in
        fun f -> odfl f (h_red_opt delta hyps f)
      else fun f -> f in

    let ax = EcEnv.Ax.by_path p env in
    let bds, rl = EcFol.decompose_forall (simp ax.EcDecl.ax_spec) in

    let bds =
      let filter = function
        | (x, GTty ty) -> (x, ty)
        | _ -> raise (InvalidUserRule RuleDependsOnMemOrModule)
      in List.map filter bds in

    let lhs, rhs, conds =
      try
        let rec doit conds f =
          match sform_of_form (simp f) with
          | SFimp (f1, f2) -> doit (f1 :: conds) f2
          | SFeq  (f1, f2) -> (f1, f2, List.rev conds)
          | _ -> raise (InvalidUserRule NotAnEq)
        in doit [] rl

      with InvalidUserRule NotAnEq
             when opts.EcTheory.ur_eqtrue &&
                  ty_equal tbool (EcEnv.ty_hnorm rl.f_ty env)
           -> (rl, f_true, List.rev [])

    in

    let rule =
      let rec rule (f : form) : EcTheory.rule_pattern =
        match EcFol.destr_app f with
        | { f_node = Fop (p, tys) }, args ->
            R.Rule (`Op (p, tys), List.map rule args)
        | { f_node = Ftuple args }, [] ->
            R.Rule (`Tuple, List.map rule args)
        | { f_node = Fint i }, [] ->
            R.Int i
        | { f_node = Flocal x }, [] ->
            R.Var x
        | _ -> raise (InvalidUserRule NotFirstOrder)
      in rule lhs in

    let lvars, ltyvars =
      let rec doit (lvars, ltyvars) = function
        | R.Var x ->
            (Sid.add x lvars, ltyvars)

        | R.Int _ ->
            (lvars, ltyvars)

        | R.Rule (op, args) ->
            let ltyvars =
              match op with
              | `Op (_, tys) ->
                List.fold_left (
                    let rec doit ltyvars = function
                      | { ty_node = Tvar a } -> Sid.add a ltyvars
                      | _ as ty -> ty_fold doit ltyvars ty in doit)
                  ltyvars tys
              | `Tuple -> ltyvars in
            List.fold_left doit (lvars, ltyvars) args

      in doit (Sid.empty, Sid.empty) rule in

    let mvars   =
      Sid.diff (Sid.of_list (List.map fst bds)) lvars in
    let mtyvars =
      Sid.diff (Sid.of_list (List.map fst ax.EcDecl.ax_tparams)) ltyvars in

    if not (Sid.is_empty mvars) then
      raise (InvalidUserRule (MissingVarInLhs (Sid.choose mvars)));
    if not (Sid.is_empty mtyvars) then
      raise (InvalidUserRule (MissingTyVarInLhs (Sid.choose mtyvars)));

    begin match rule with
    | R.Var _ -> raise (InvalidUserRule (HeadedByVar));
    | _       -> () end;

    R.{ rl_tyd  = ax.EcDecl.ax_tparams;
        rl_vars = bds;
        rl_cond = conds;
        rl_ptn  = rule;
        rl_tg   = rhs;
        rl_prio = prio; }

end
