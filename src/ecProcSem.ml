(* -------------------------------------------------------------------- *)
open EcUtils
open EcSymbols
open EcAst
open EcTypes
open EcModules
open EcFol

module BI = EcBigInt

(* -------------------------------------------------------------------- *)
exception SemNotSupported

(* -------------------------------------------------------------------- *)
type senv = {
  env   : EcEnv.env;
  subst : EcIdent.t Msym.t;
}

(* -------------------------------------------------------------------- *)
module Env = struct
  let empty (env : EcEnv.env) =
    { env; subst = Msym.empty; }

  let fresh (env : senv) (x : symbol) =
    let idx = EcIdent.create x in
    let env = { env with subst = Msym.add x idx env.subst } in
    (env, idx)
end

(* -------------------------------------------------------------------- *)
type mode = [`Det | `Distr]

(* -------------------------------------------------------------------- *)
(* FIXME: MOVE ME                                                       *)
let eop_dunit (ty : ty) =
  e_op EcCoreLib.CI_Distr.p_dunit [ty] (tfun ty (tdistr ty))

let e_dunit (e : expr) =
  e_app (eop_dunit e.e_ty) [e] (tdistr e.e_ty)

(* -------------------------------------------------------------------- *)
let rec translate_i (env : senv) (cont : senv -> mode * expr) (i : instr) =
  EcPV.PV.iter
    (fun pv _ -> if not (is_loc pv) then raise SemNotSupported)
    (fun _ -> raise SemNotSupported)
    (EcPV.i_read env.env i);

  let wr =
    let do1 (pv, ty) =
      match pv with
      | PVglob _ -> raise SemNotSupported
      | PVloc  x -> (x, ty) in

    let wr, mods = EcPV.PV.elements (EcPV.i_write env.env i) in

    if not (List.is_empty mods) then
      raise SemNotSupported;
    List.map do1 wr
  in

  let env', ids =
    List.fold_left_map
      (fun env (x, _) -> Env.fresh env x)
      env wr in

  let ids = List.combine wr ids in

  match i.i_node with
  | Sasgn (lv, e) ->
     let e = translate_e env e in
     let lv = translate_lv env' lv in
     let mode, body = cont env' in
     (mode, (e_let lv e body))

  | Srnd (lv, d) -> begin
     let d = translate_e env d in
     let lv = translate_lv env' lv in
     let mode, body = cont env' in

     let tya = oget (as_tdistr (EcEnv.Ty.hnorm d.e_ty env.env)) in
     let tyb = body.e_ty in

     let aout =
       let d    = form_of_expr mhr d in
       let body = form_of_expr mhr body in
       let body =
         let arg  = EcIdent.create "arg" in
         let body = f_let lv (f_local arg tya) body in
         f_lambda [(arg, GTty tya)] body in

       match mode with
       | `Det   -> f_dmap tya tyb d body
       | `Distr -> f_dlet_simpl tya (oget (as_tdistr tyb)) d body

     in (`Distr, expr_of_form mhr aout)
    end

  | Sif (e, bt, bf) ->
     let cont (fenv : senv) : mode * expr =
       let do1 ((x, ty), _) =
         e_local (Msym.find x fenv.subst) ty in
       let vars = List.map do1 ids in
       (`Det, e_tuple vars) in

     let e  = translate_e env e in
     let bt = translate_s env cont bt in
     let bf = translate_s env cont bf in

     let mode, (bt, bf) =
       match bt, bf with
       | (`Det, bt), (`Det, bf) ->
          (`Det, (bt, bf))

       | (`Distr, bt), (`Distr, bf) ->
          (`Distr, (bt, bf))

       | (`Det, bt), (`Distr, bf) ->
          (`Distr, (e_dunit bt, bf))

       | (`Distr, bt), (`Det, bf) ->
          (`Distr, (bt, e_dunit bf)) in

     let lv =
       let ids =
         let do1 ((x, ty), _) =
           (Msym.find x env'.subst, ty) in
         List.map do1 ids in

       match ids with
       | [] ->
          LSymbol (EcIdent.create "_", tunit)
       | [x, ty] ->
          LSymbol (x, ty)
       | ids ->
          LTuple ids in

     let cmode, c = (cont env') in

     begin
       match mode, cmode with
       | `Det, _ ->
          (cmode, e_let lv (e_if e bt bf) c)

       | `Distr, `Det ->
          let body = form_of_expr mhr (e_if e bt bf) in
          let tya  = oget (as_tdistr body.f_ty) in
          let v    = EcIdent.create "v" in
          let vx   = f_local v tya in
          let aout =
            f_dmap
              tya
              c.e_ty
              body
              (f_lambda
                 [v, GTty tya]
                 (f_let lv vx (form_of_expr mhr c)))

          in (`Distr, expr_of_form mhr aout)

       | `Distr, `Distr ->
          let body = form_of_expr mhr (e_if e bt bf) in
          let tya  = oget (as_tdistr body.f_ty) in
          let tyb  = oget (as_tdistr c.e_ty) in
          let v    = EcIdent.create "v" in
          let vx   = f_local v tya in
          let aout =
            f_dlet_simpl
              tya
              tyb
              body
              (f_lambda
                 [v, GTty tya]
                 (f_let lv vx (form_of_expr mhr c)))

          in (`Distr, expr_of_form mhr aout)

     end

  | Scall (Some lv, ({ x_top = { m_top = `Concrete (p, _) }; x_sub = f } as xp), args)  ->
      let fd   = oget (EcEnv.Fun.by_xpath_opt xp env.env) in
      let args = translate_e env (e_tuple args) in
      let op   = EcPath.pqname (oget (EcPath.prefix p)) f in
      let op   = e_op op [] (tfun fd.f_sig.fs_arg fd.f_sig.fs_ret) in
      let op   = e_app op [args] fd.f_sig.fs_ret in
      let lv   = translate_lv env' lv  in

      let cmode, c = cont env' in

      (cmode, e_let lv op c)

  | Swhile    _
  | Smatch    _
  | Sassert   _
  | Sabstract _
  | Scall     _ ->
     raise SemNotSupported;

(* -------------------------------------------------------------------- *)
and translate_s (env : senv) (cont : senv -> mode * expr) (s : stmt) =
  match translate_forloop env cont s with
  | Some e ->
     e
  | None ->
     match s.s_node with
     | [] ->
        cont env
     | i :: s ->
        translate_i env (fun env -> translate_s env cont (stmt s)) i

(* -------------------------------------------------------------------- *)
and translate_forloop (env : senv) (cont : senv -> mode * expr) (s : stmt) =
  let module ET = EcReduction.EqTest in

  match s.s_node with
  | { i_node = Sasgn (LvVar (PVloc x, xty), e) } :: { i_node = Swhile (c, body) } :: s_tail ->
     if not (ET.for_type env.env xty tint) then
       raise SemNotSupported;

     if not (ET.for_expr env.env e (e_int EcBigInt.zero)) then
       raise SemNotSupported;

     let inc, body =
       let inc, body =
         match List.rev body.s_node with
         | inc :: body -> inc, List.rev body
         | _ -> raise SemNotSupported in

       match inc.i_node with
       | Sasgn (LvVar (PVloc y, _), ic) ->
          if x <> y then
            raise SemNotSupported
          else begin
            match ic.e_node with
            | Eapp ({ e_node = Eop (op, []) }, [{ e_node = Evar (PVloc y') }; { e_node = Eint inc }])
                 when    y = y'
                      && EcBigInt.lt EcBigInt.zero inc
                      && EcPath.p_equal op EcCoreLib.CI_Int.p_int_add
              -> inc, body
            | _ -> raise SemNotSupported
          end;
       | _ -> raise SemNotSupported in

     let body =
       if BI.gt inc BI.one then begin
         let mx =
           e_app
             (e_op EcCoreLib.CI_Int.p_int_mul [] (toarrow [tint; tint] tint))
             [e_int inc; e_var (pv_loc x) tint] tint in
         let subst = EcPV.Mpv.add env.env (pv_loc x) mx EcPV.Mpv.empty in
         EcPV.Mpv.issubst env.env subst body
       end else body in

     let bd =
       match c.e_node with
       | Eapp ({ e_node = Eop (op, []) }, [{ e_node = Evar (PVloc y) }; bd])
            when    x = y
                 && EcPath.p_equal op EcCoreLib.CI_Int.p_int_lt -> bd
       | _ -> raise SemNotSupported in

     let wr = EcPV.s_write env.env (EcModules.stmt body) in

     if EcPV.PV.mem_pv env.env (pv_loc x) wr then
       raise SemNotSupported;

     if not (EcPV.PV.indep env.env (EcPV.e_read env.env bd) wr) then
       raise SemNotSupported;

     EcPV.PV.iter
       (fun pv _ -> if not (is_loc pv) then raise SemNotSupported)
       (fun _ -> raise SemNotSupported)
       (EcPV.is_read env.env body);

     let wr =
       let do1 (pv, ty) =
         match pv with
         | PVglob _ -> raise SemNotSupported
         | PVloc  z -> (z, ty) in

       let wr, mods = EcPV.PV.elements (EcPV.is_write env.env body) in

       if not (List.is_empty mods) then
         raise SemNotSupported;
       List.map do1 wr
     in

     let wr = List.filter (fun (z, _) -> z <> x) wr in

     let mode, body, _ =
       let env', ids =
         List.fold_left_map
           (fun env (x, _) -> Env.fresh env x)
           env wr in

       let ids = List.combine wr ids in

       let env', x = Env.fresh env' x in

       let cont_body (fenv : senv) : mode * expr =
         let do1 ((x, ty), _) =
           e_local (Msym.find x fenv.subst) ty in
         let vars = List.map do1 ids in
         (`Det, e_tuple vars) in

       let bmode, body = translate_s env' cont_body (stmt body) in

       let body =
         match ids with
         | [] ->
            e_lam [(EcIdent.create "_", tunit)] body
         | [((_, ty), z)] ->
            e_lam [(z, ty)] body
         | ids ->
            let arg = EcIdent.create "arg" in
            let aty = ttuple (List.map (fun ((_, ty), _) -> ty) ids) in
            let lv  = LTuple (List.map (fun ((_, ty), z) -> (z, ty)) ids) in
            e_lam
              [(arg, aty)]
              (e_let lv (e_local arg aty) body) in

       let body = e_lam [(x, tint)] body in

       bmode, body, ids in

     let env', ids =
       List.fold_left_map
         (fun env (x, _) -> Env.fresh env x)
         env wr in

     let ids = List.combine wr ids in
     let aty = ttuple (List.map (fun ((_, ty), _) -> ty) ids) in

     let env', x = Env.fresh env' x in

     let lv =
       let ids =
         let do1 ((x, ty), _) =
           (Msym.find x env'.subst, ty) in
         List.map do1 ids in

       match ids with
       | [] ->
          LSymbol (EcIdent.create "_", tunit)
       | [x, ty] ->
          LSymbol (x, ty)
       | ids ->
          LTuple ids in

     let niter = form_of_expr mhr (translate_e env bd) in
     let niter = f_proj_simpl (f_int_edivz_simpl niter (f_int inc)) 0 tint in
     let rem   = f_proj_simpl (f_int_edivz_simpl niter (f_int inc)) 1 tint in
     let outv  = f_int_add_simpl (f_int_mul_simpl niter (f_int inc)) rem in

     let niter = expr_of_form mhr niter in
     let outv  = expr_of_form mhr outv in

     let mode, aout =
       match mode with
       | `Det ->
          let args =
            List.map
              (fun (z, zty) ->
                match Msym.find_opt z env.subst with
                | None -> e_op EcCoreLib.CI_Witness.p_witness [zty] zty
                | Some z -> e_local z zty)
              wr in
          let args = e_tuple args in
          let cmode, c = translate_s env' cont (stmt s_tail) in
          let aout = e_op EcCoreLib.CI_Int.p_iteri [aty] in
          let aout = aout (toarrow [tint; (toarrow [tint; aty] aty); aty] aty) in
          let aout = e_app aout [niter; body; args] aty in
          (cmode, e_let lv aout c)

       | `Distr ->
          let args =
            List.map
              (fun (z, zty) ->
                match Msym.find_opt z env.subst with
                | None -> e_op EcCoreLib.CI_Witness.p_witness [zty] zty
                | Some z -> e_local z zty)
              wr in
          let args = e_tuple args in
          let cmode, c = translate_s env' cont (stmt s_tail) in
          let aout = e_op EcCoreLib.CI_Distr.p_dfold [aty] in
          let aout = aout (toarrow [toarrow [tint; aty] (tdistr aty); aty; tint] (tdistr aty)) in
          let aout = e_app aout [body; args; niter] (tdistr aty) in

          let arg = EcIdent.create "arg" in

          let ctor =
            match cmode with
            | `Det   -> f_dmap
            | `Distr -> f_dlet_simpl in

          let aout =
            ctor
              aty c.e_ty
              (form_of_expr mhr aout)
              (f_lambda
                 [(arg, GTty aty)]
                 (f_let lv (f_local arg aty) (form_of_expr mhr c))) in
          (`Distr, expr_of_form mhr aout)

     in Some (mode, e_let (LSymbol (x, tint)) outv aout)

  | _ ->
     None

(* -------------------------------------------------------------------- *)
and translate_e (env : senv) (e : expr) =
  match e.e_node with
  | Evar (PVloc x) ->
     e_local (oget (Msym.find_opt x env.subst)) e.e_ty

  | Evar (PVglob _) ->
     raise SemNotSupported

  | _ ->
     e_map (fun x -> x) (translate_e env) e

(* -------------------------------------------------------------------- *)
and translate_lv (env : senv) (lv : lvalue) : lpattern =
  match lv with
  | LvVar (pv, ty) ->
     LSymbol (translate_pv env pv, ty)

  | LvTuple pvs ->
     let do1 (pv, ty) =
       (translate_pv env pv, ty)
     in LTuple (List.map do1 pvs)

(* -------------------------------------------------------------------- *)
and translate_pv (env : senv) (pv : prog_var) =
  match pv with
  | PVglob _ ->
     raise SemNotSupported
  | PVloc x ->
      oget (Msym.find_opt x env.subst)
