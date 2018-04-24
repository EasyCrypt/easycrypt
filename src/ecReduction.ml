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

    let check_lpattern alpha lp1 lp2 =
      match lp1, lp2 with
      | LSymbol (id1,_), LSymbol (id2,_) ->
          Mid.add id1 id2 alpha

      | LTuple lid1, LTuple lid2 when List.length lid1 = List.length lid2 ->
          List.fold_left2
            (fun alpha (id1,_) (id2,_) -> Mid.add id1 id2 alpha)
            alpha lid1 lid2

      | _, _ -> raise E.NotConv in

    let check_binding env alpha (id1, ty1) (id2, ty2) =
      if not (for_type env ty1 ty2) then
        raise E.NotConv;
      Mid.add id1 id2 alpha in

    let check_bindings env alpha b1 b2 =
      if List.length b1 <> List.length b2 then
        raise E.NotConv;
      List.fold_left2 (check_binding env) alpha b1 b2 in

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

    in fun e1 e2 -> aux Mid.empty e1 e2

  (* ------------------------------------------------------------------ *)
  let for_lv env ~norm lv1 lv2 =
    match lv1, lv2 with
    | LvVar(p1, _), LvVar(p2, _) ->
        for_pv env ~norm p1 p2

    | LvTuple p1, LvTuple p2 ->
        List.all2
          (fun (p1, _) (p2, _) -> for_pv env ~norm p1 p2)
          p1 p2

    | LvMap ((m1, ty1), p1, e1, _), LvMap ((m2, ty2), p2, e2, _) ->
        p_equal m1 m2
          && List.all2 (for_type env) ty1 ty2
          && for_pv env ~norm p1 p2
          && for_expr env ~norm e1 e2

    | _, _ -> false

  (* ------------------------------------------------------------------ *)
  let rec for_stmt env ~norm s1 s2 =
       s_equal s1 s2
    || List.all2 (for_instr env ~norm) s1.s_node s2.s_node

  (* ------------------------------------------------------------------ *)
  and for_instr env ~norm i1 i2 =
    i_equal i1 i2 || for_instr_r env ~norm i1 i2

  and for_instr_r env ~norm i1 i2 =
    match i1.i_node, i2.i_node with
    | Sasgn (lv1, e1), Sasgn (lv2, e2) ->
        for_lv env ~norm lv1 lv2 && for_expr env ~norm e1 e2

    | Srnd (lv1, e1), Srnd (lv2, e2) ->
        for_lv env ~norm lv1 lv2 && for_expr env ~norm e1 e2

    | Scall (lv1, f1, e1), Scall (lv2, f2, e2) ->
        oall2 (for_lv env ~norm) lv1 lv2
          && for_xp env ~norm f1 f2
          && List.all2 (for_expr env ~norm) e1 e2

    | Sif (a1, b1, c1), Sif(a2, b2, c2) ->
        for_expr env ~norm a1 a2
          && for_stmt env ~norm b1 b2
          && for_stmt env ~norm c1 c2

    | Swhile(a1,b1), Swhile(a2,b2) ->
        for_expr env ~norm a1 a2 && for_stmt env ~norm b1 b2

    | Sassert a1, Sassert a2 ->
        for_expr env ~norm a1 a2

    | Sabstract id1, Sabstract id2 ->
        EcIdent.id_equal id1 id2

    | _, _ -> false

  (* ------------------------------------------------------------------ *)
  let for_pv    = fun env ?(norm = true) -> for_pv    env ~norm
  let for_xp    = fun env ?(norm = true) -> for_xp    env ~norm
  let for_mp    = fun env ?(norm = true) -> for_mp    env ~norm
  let for_instr = fun env ?(norm = true) -> for_instr env ~norm
  let for_stmt  = fun env ?(norm = true) -> for_stmt  env ~norm
  let for_expr  = fun env ?(norm = true) -> for_expr  env ~norm
end

(* -------------------------------------------------------------------- *)
type reduction_info = {
  beta    : bool;
  delta_p : (path  -> bool);
  delta_h : (ident -> bool);
  zeta    : bool;
  iota    : bool;
  eta     : bool;
  logic   : rlogic_info;
  modpath : bool;
}

and rlogic_info = [`Full | `ProductCompat] option

(* -------------------------------------------------------------------- *)

let full_red = {
  beta    = true;
  delta_p = EcUtils.predT;
  delta_h = EcUtils.predT;
  zeta    = true;
  iota    = true;
  eta     = true;
  logic   = Some `Full;
  modpath = true;
}

let no_red = {
  beta    = false;
  delta_p = EcUtils.pred0;
  delta_h = EcUtils.pred0;
  zeta    = false;
  iota    = false;
  eta     = false;
  logic   = None;
  modpath = false;
}

let beta_red     = { no_red with beta = true; }
let betaiota_red = { no_red with beta = true; iota = true; }

let nodelta =
  { full_red with
      delta_h = EcUtils.pred0;
      delta_p = EcUtils.pred0; }

let reduce_local ri hyps x  =
  if   ri.delta_h x
  then LDecl.unfold x hyps
  else raise NotReducible

let reduce_op ri env p tys =
  if   ri.delta_p p
  then Op.reduce env p tys
  else raise NotReducible

let is_record env f =
  match EcFol.destr_app f with
  | { f_node = Fop (p, _) }, _ -> EcEnv.Op.is_record_ctor env p
  | _ -> false

(* -------------------------------------------------------------------- *)
let rec h_red ri env hyps f =
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
  | Flet (LTuple ids, { f_node = Ftuple es }, e2) when ri.iota ->
      let s =
        List.fold_left2
          (fun s (x,_) e1 -> Fsubst.f_bind_local s x e1)
          Fsubst.f_subst_id ids es
      in
        Fsubst.f_subst s e2

    (* ι-reduction (let-records) *)
  | Flet (LRecord (_, ids), f1, f2) when ri.iota && is_record env f1 ->
      let args  = snd (EcFol.destr_app f1) in
      let subst =
        List.fold_left2 (fun subst (x, _) e ->
          match x with
          | None   -> subst
          | Some x -> Fsubst.f_bind_local subst x e)
          Fsubst.f_subst_id ids args
      in
        Fsubst.f_subst subst f2

    (* ι-reduction (records projection) *)
  | Fapp ({ f_node = Fop (p, _); } as f1, args)
      when ri.iota && EcEnv.Op.is_projection env p -> begin
        try
          match args with
          | [mk] -> begin
              match (odfl mk (h_red_opt ri env hyps mk)).f_node with
              | Fapp ({ f_node = Fop (mkp, _) }, mkargs) ->
                  if not (EcEnv.Op.is_record_ctor env mkp) then
                    raise NotReducible;
                  let v = oget (EcEnv.Op.by_path_opt p env) in
                  let v = proj3_2 (EcDecl.operator_as_proj v) in
                  let v = List.nth mkargs v in
                    odfl v (h_red_opt ri env hyps v)
              | _ -> raise NotReducible
            end
          | _ -> raise NotReducible

        with NotReducible ->
          f_app (h_red ri env hyps f1) args f.f_ty
      end

    (* ι-reduction (tuples projection) *)
  | Fproj(f1, i) when ri.iota ->
      let f' = f_proj_simpl f1 i f.f_ty in
        if f_equal f f' then f_proj (h_red ri env hyps f1) i f.f_ty else f'

    (* ι-reduction (if-then-else) *)
  | Fif (f1, f2, f3) when ri.iota ->
      let f' = f_if_simpl f1 f2 f3 in
        if f_equal f f' then f_if (h_red ri env hyps f1) f2 f3 else f'

    (* ι-reduction (match-fix) *)
  | Fapp ({ f_node = Fop (p, tys); } as f1, fargs)
      when ri.iota && EcEnv.Op.is_fix_def env p -> begin

        try
          let op  = oget (EcEnv.Op.by_path_opt p env) in
          let fix = EcDecl.operator_as_fix op in

            if List.length fargs <> snd (fix.EcDecl.opf_struct) then
              raise NotReducible;

          let args  = Array.of_list fargs in
          let pargs = List.fold_left (fun (opb, acc) v ->
              let v = args.(v) in
              let v = odfl v (h_red_opt ri env hyps v) in

                match fst_map (fun x -> x.f_node) (EcFol.destr_app v) with
                | (Fop (p, _), cargs) when EcEnv.Op.is_dtype_ctor env p -> begin
                    let idx = EcEnv.Op.by_path p env in
                    let idx = snd (EcDecl.operator_as_ctor idx) in
                      match opb with
                      | EcDecl.OPB_Leaf   _  -> assert false
                      | EcDecl.OPB_Branch bs ->
                         ((Parray.get bs idx).EcDecl.opb_sub, cargs :: acc)
                  end
                | _ -> raise NotReducible)
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

            Fsubst.f_subst subst body

        with NotReducible ->
          f_app (h_red ri env hyps f1) fargs f.f_ty
    end

    (* μ-reduction *)
  | Fglob (mp, m) when ri.modpath ->
      let f' = EcEnv.NormMp.norm_glob env m mp in
        if f_equal f f' then raise NotReducible else f'

    (* μ-reduction *)
  | Fpvar (pv, m) when ri.modpath ->
      let pv' = EcEnv.NormMp.norm_pvar env pv in
        if pv_equal pv pv' then raise NotReducible else f_pvar pv' f.f_ty m

    (* logical reduction *)
  | Fapp ({f_node = Fop (p, tys); } as fo, args)
      when is_some ri.logic && is_logical_op p
    ->
     let pcompat =
       match oget ri.logic with `Full -> true | `ProductCompat -> false
     in

      let f' =
        match op_kind p, args with
        | Some (`Not), [f1]    when pcompat -> f_not_simpl f1
        | Some (`Imp), [f1;f2] when pcompat -> f_imp_simpl f1 f2
        | Some (`Iff), [f1;f2] when pcompat -> f_iff_simpl f1 f2


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
        | Some (`Real_add ), [f1;f2] -> f_real_add_simpl f1 f2
        | Some (`Real_opp ), [f]     -> f_real_opp_simpl f
        | Some (`Real_mul ), [f1;f2] -> f_real_mul_simpl f1 f2
        | Some (`Real_inv ), [f]     -> f_real_inv_simpl f
        | Some (`Eq       ), [f1;f2] -> begin
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

        | _ when ri.delta_p p ->
            let op = reduce_op ri env p tys in
            f_app_simpl op args f.f_ty

        | _ -> f
      in
        if   f_equal f f'
        then f_app fo (h_red_args ri env hyps args) f.f_ty
        else f'

    (* δ-reduction *)
  | Fop (p, tys) ->
      reduce_op ri env p tys

    (* δ-reduction *)
  | Fapp ({ f_node = Fop (p, tys) }, args) when ri.delta_p p ->
      let op = reduce_op ri env p tys in
      f_app_simpl op args f.f_ty

    (* η-reduction *)
  | Fquant (Llambda, [x, GTty _], { f_node = Fapp (fn, args) })
      when can_eta x (fn, args)
    -> f_app fn (List.take (List.length args - 1) args) f.f_ty

    (* contextual rule - let *)
  | Flet (lp, f1, f2) -> f_let lp (h_red ri env hyps f1) f2

    (* Contextual rule - application args. *)
  | Fapp (f1, args) ->
      f_app (h_red ri env hyps f1) args f.f_ty

    (* Contextual rule - bindings *)
  | Fquant (Lforall as t, b, f1)
  | Fquant (Lexists as t, b, f1) when ri.logic = Some `Full -> begin
      let ctor = match t with
        | Lforall -> f_forall_simpl
        | Lexists -> f_exists_simpl
        | _       -> assert false in

      try
        let env = Mod.add_mod_binding b env in
          ctor b (h_red ri env hyps f1)
      with NotReducible ->
        let f' = ctor b f1 in
          if f_equal f f' then raise NotReducible else f'
    end

  | _ -> raise NotReducible

and can_eta x (f, args) =
  match List.rev args with
  | { f_node = Flocal y } :: args ->
      let check v = not (Mid.mem x v.f_fv) in
      id_equal x y && List.for_all check (f :: args)
  | _ -> false

and h_red_args ri env hyps args =
  match args with
  | [] -> raise NotReducible
  | a :: args ->
    try h_red ri env hyps a :: args
    with NotReducible -> a :: h_red_args ri env hyps args

and h_red_opt ri env hyps f =
  try Some (h_red ri env hyps f)
  with NotReducible -> None

and check_alpha_equal ri hyps f1 f2 =
  let env = LDecl.toenv hyps in
  let exn = IncompatibleForm (env, (f1, f2)) in
  let error () = raise exn in
  let ensure t = if not t then error () in

  let check_ty env subst ty1 ty2 =
    ensure (EqTest.for_type env ty1 (subst.fs_ty ty2)) in

  let add_local (env, subst) (x1,ty1) (x2,ty2) =
    check_ty env subst ty1 ty2;
    env,
    if id_equal x1 x2 then subst
    else Fsubst.f_bind_rename subst x2 x1 ty1 in

  let check_lpattern env subst lp1 lp2 =
    match lp1, lp2 with
    | LSymbol xt1, LSymbol xt2 -> add_local (env, subst) xt1 xt2
    | LTuple lid1, LTuple lid2 when List.length lid1 = List.length lid2 ->
      List.fold_left2 add_local (env,subst) lid1 lid2
    | _, _ -> error() in

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
    | _, _ -> error () in

  (* TODO all declaration in env, do it also in add local *)
  let check_binding (env, subst) (x1,gty1) (x2,gty2) =
    let gty2 = Fsubst.gty_subst subst gty2 in
    match gty1, gty2 with
    | GTty ty1, GTty ty2 ->
      ensure (EqTest.for_type env ty1 ty2);
      env,
      if id_equal x1 x2 then subst else
        Fsubst.f_bind_rename subst x2 x1 ty1
    | GTmodty (p1, r1) , GTmodty(p2, r2) ->
      ensure (ModTy.mod_type_equiv env p1 p2 &&
                NormMp.equal_restr env r1 r2);
      Mod.bind_local x1 p1 r1 env,
      if id_equal x1 x2 then subst
      else Fsubst.f_bind_mod subst x2 (EcPath.mident x1)
    | GTmem   me1, GTmem me2  ->
      check_memtype env me1 me2;
      env,
      if id_equal x1 x2 then subst
      else Fsubst.f_bind_mem subst x2 x1
    | _, _ -> error () in

  let check_bindings env subst bd1 bd2 =
    List.fold_left2 check_binding (env,subst) bd1 bd2 in

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

  let rec aux1 env subst f1 f2 =
    if Fsubst.is_subst_id subst && f_equal f1 f2 then ()
    else match f1.f_node, f2.f_node with

    | Fquant(q1,bd1,f1'), Fquant(q2,bd2,f2') when
        q1 = q2 && List.length bd1 = List.length bd2 ->
      let env, subst = check_bindings env subst bd1 bd2 in
      aux env subst f1' f2'

    | Fif(a1,b1,c1), Fif(a2,b2,c2) ->
      aux env subst a1 a2; aux env subst b1 b2; aux env subst c1 c2

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

  and aux env subst f1 f2 =
    try aux1 env subst f1 f2
    with e when e == exn ->
      match h_red_opt ri env hyps f1 with
      | Some f1 -> aux env subst f1 f2
      | None ->
        match h_red_opt ri env hyps f2 with
        | Some f2 -> aux env subst f1 f2
        | None when EqTest.for_type env f1.f_ty f2.f_ty -> begin
            let ty, codom =
              match f1.f_node, f2.f_node with
              | Fquant (Llambda, (_, GTty ty) :: bd, f1'), _ ->
                  ty, toarrow (List.map (gty_as_ty |- snd) bd) f1'.f_ty
              | _,  Fquant(Llambda, (_, GTty ty) :: bd, f2') ->
                  ty, toarrow (List.map (gty_as_ty |- snd) bd) f2'.f_ty
              | _, _ -> raise e
            in

              let x  = f_local (EcIdent.create "_") ty in
              let f1 = f_app_simpl f1 [x] codom in
              let f2 = f_app_simpl f2 [x] codom in
              aux env subst f1 f2
        end
        | _ -> raise e

  in aux env Fsubst.f_subst_id f1 f2

and check_alpha_eq f1 f2 = check_alpha_equal no_red   f1 f2
and check_conv     f1 f2 = check_alpha_equal full_red f1 f2

and is_alpha_eq hyps f1 f2 =
  try check_alpha_eq hyps f1 f2; true
  with _ -> false

let is_conv hyps f1 f2 =
  try check_conv hyps f1 f2; true
  with _ -> false

let h_red ri hyps f =
   h_red ri (LDecl.toenv hyps) hyps f

let h_red_opt ri hyps f = h_red_opt ri (LDecl.toenv hyps) hyps f

let rec simplify ri hyps f =
  let f' = try h_red ri hyps f with NotReducible -> f in
  if   f == f'
  then simplify_rec ri hyps f
  else simplify ri hyps f'

and simplify_rec ri hyps f =
  match f.f_node with

  | Fapp ({ f_node = Fop _ } as fo, args) ->
      let args' = List.map (simplify ri hyps) args in
      let app1  = (fo, args , f.f_ty) in
      let app2  = (fo, args', f.f_ty) in
      let f'    =  EcFol.FSmart.f_app (f, app1) app2 in
      (try h_red ri hyps f' with NotReducible -> f')

  | FhoareF hf when ri.modpath ->
      let hf_f = EcEnv.NormMp.norm_xfun (LDecl.toenv hyps) hf.hf_f in
      f_map (fun ty -> ty) (simplify ri hyps) (f_hoareF_r { hf with hf_f })

  | FbdHoareF hf when ri.modpath ->
      let bhf_f = EcEnv.NormMp.norm_xfun (LDecl.toenv hyps) hf.bhf_f in
      f_map (fun ty -> ty) (simplify ri hyps) (f_bdHoareF_r { hf with bhf_f })

  | FequivF ef when ri.modpath ->
      let ef_fl = EcEnv.NormMp.norm_xfun (LDecl.toenv hyps) ef.ef_fl in
      let ef_fr = EcEnv.NormMp.norm_xfun (LDecl.toenv hyps) ef.ef_fr in
      f_map (fun ty -> ty) (simplify ri hyps) (f_equivF_r { ef with ef_fl; ef_fr; })

  | FeagerF eg when ri.modpath ->
      let eg_fl = EcEnv.NormMp.norm_xfun (LDecl.toenv hyps) eg.eg_fl in
      let eg_fr = EcEnv.NormMp.norm_xfun (LDecl.toenv hyps) eg.eg_fr in
      f_map (fun ty -> ty) (simplify ri hyps) (f_eagerF_r { eg with eg_fl ; eg_fr; })

  | Fpr pr  when ri.modpath ->
      let pr_fun = EcEnv.NormMp.norm_xfun (LDecl.toenv hyps) pr.pr_fun in
      f_map (fun ty -> ty) (simplify ri hyps) (f_pr_r { pr with pr_fun })

  | _ -> f_map (fun ty -> ty) (simplify ri hyps) f

(* -------------------------------------------------------------------- *)
type xconv = [`Eq | `AlphaEq | `Conv]

let xconv (mode : xconv) hyps =
  match mode with
  | `Eq      -> f_equal
  | `AlphaEq -> is_alpha_eq hyps
  | `Conv    -> is_conv hyps
