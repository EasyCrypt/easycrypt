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
open EcSymbols
open EcTypes
open EcDecl
open EcModules
open EcFol

open EcCoreGoal
open EcLowPhlGoal

(* -------------------------------------------------------------------- *)
module Low = struct
  (* ------------------------------------------------------------------ *)
  let gen_rcond pf b m at_pos s =
    let head, i, tail = s_split_i at_pos s in
    let e, s =
      match i.i_node with
      | Sif(e,s1,s2) -> e, if b then s1.s_node else s2.s_node
      | Swhile(e,s1) -> e, if b then s1.s_node@[i] else []
      | _ ->
          tc_error_lazy pf (fun fmt ->
            Format.fprintf fmt
              "the targetted instruction is not a conditionnal")
    in
    let f_e = form_of_expr m e in
    let f_e = if b then f_e else f_not f_e in

    (stmt head, e, f_e, stmt (head @ s @ tail))

  (* ------------------------------------------------------------------ *)
  let t_hoare_rcond_r b at_pos tc =
    let hs = tc1_as_hoareS tc in
    let m  = EcMemory.memory hs.hs_m in
    let hd,_,e,s = gen_rcond !!tc b m at_pos hs.hs_s in
    let concl1  = f_hoareS_r { hs with hs_s = hd; hs_po = e } in
    let concl2  = f_hoareS_r { hs with hs_s = s } in
    FApi.xmutate1 tc `RCond [concl1; concl2]

  (* ------------------------------------------------------------------ *)
  let t_choare_rcond_r b at_pos c tc =
    let c = EcUtils.odfl f_true c in

    let chs = tc1_as_choareS tc in
    let m  = EcMemory.memory chs.chs_m in
    let hd,e_expr,e,s = gen_rcond !!tc b m at_pos chs.chs_s in
    let cond, cost =
      EcCHoare.cost_sub_self
        chs.chs_co
        (EcCHoare.cost_of_expr c chs.chs_m e_expr) in
    let concl1  =
      f_hoareS chs.chs_m chs.chs_pr hd (f_and_simpl c e) in
    let concl2  = f_cHoareS_r { chs with chs_s = s;
                                         chs_co = cost; } in
    FApi.xmutate1 tc `RCond [concl1; cond; concl2]

  (* ------------------------------------------------------------------ *)
  let t_bdhoare_rcond_r b at_pos tc =
    let bhs = tc1_as_bdhoareS tc in
    let m  = EcMemory.memory bhs.bhs_m in
    let hd,_,e,s = gen_rcond !!tc b m at_pos bhs.bhs_s in
    let concl1  = f_hoareS bhs.bhs_m bhs.bhs_pr hd e in
    let concl2  = f_bdHoareS_r { bhs with bhs_s = s } in
    FApi.xmutate1 tc `RCond [concl1; concl2]

  (* ------------------------------------------------------------------ *)
  let t_equiv_rcond_r side b at_pos tc =
    let es = tc1_as_equivS tc in
    let m,mo,s =
      match side with
      | `Left  -> es.es_ml,es.es_mr, es.es_sl
      | `Right -> es.es_mr,es.es_ml, es.es_sr in
    let hd,_,e,s = gen_rcond !!tc b EcFol.mhr at_pos s in
    let mo' = EcIdent.create "&m" in
    let s1 = Fsubst.f_subst_id in
    let s1 = Fsubst.f_bind_mem s1 (EcMemory.memory m) EcFol.mhr in
    let s1 = Fsubst.f_bind_mem s1 (EcMemory.memory mo) mo' in
    let pre1 = Fsubst.f_subst s1 es.es_pr in
    let concl1 =
      f_forall_mems [mo', EcMemory.memtype mo]
        (f_hoareS (EcFol.mhr, EcMemory.memtype m) pre1 hd e) in
    let sl,sr = match side with `Left -> s, es.es_sr | `Right -> es.es_sl, s in
    let concl2 = f_equivS_r { es with es_sl = sl; es_sr = sr } in
    FApi.xmutate1 tc `RCond [concl1; concl2]

  (* ------------------------------------------------------------------ *)
  let t_hoare_rcond   = FApi.t_low2 "hoare-rcond"   t_hoare_rcond_r
  let t_choare_rcond  = FApi.t_low3 "choare-rcond"  t_choare_rcond_r
  let t_bdhoare_rcond = FApi.t_low2 "bdhoare-rcond" t_bdhoare_rcond_r
  let t_equiv_rcond   = FApi.t_low3 "equiv-rcond"   t_equiv_rcond_r
end

(* -------------------------------------------------------------------- *)
let t_rcond side b at_pos c tc =
  let concl = FApi.tc1_goal tc in

  let check_none () = if c <> None then
      tc_error !!tc "optional cost is only for choare judgements" in

  match side with
  | None when is_bdHoareS concl ->
    check_none (); Low.t_bdhoare_rcond b at_pos tc
  | None when is_cHoareS concl  -> Low.t_choare_rcond b at_pos c tc
  | None ->
    check_none (); Low.t_hoare_rcond b at_pos tc
  | Some side ->
    check_none (); Low.t_equiv_rcond side b at_pos tc

let process_rcond side b at_pos c tc =
  let c = EcUtils.omap (fun c ->
      EcProofTyping.tc1_process_Xhl_formula tc c) c in

  t_rcond side b at_pos c tc

(* -------------------------------------------------------------------- *)
module LowMatch = struct
  (* ------------------------------------------------------------------ *)
  let gen_rcond (pf, env) c m at_pos s =
    let head, i, tail = s_split_i at_pos s in
    let e, infos, (cvars, subs) =
      match i.i_node with
      | Smatch (e, bs) -> begin
          let typ, tydc, tyinst = oget (EcEnv.Ty.get_top_decl e.e_ty env) in
          let tyd = oget (EcDecl.tydecl_as_datatype tydc) in
          let ctor =
            let test (_i : int) = sym_equal c -| fst in
            List.Exceptionless.findi test tyd.tydt_ctors in

          match ctor with
          | None ->
              tc_error_lazy pf (fun fmt ->
                  Format.fprintf fmt
                    "cannot find the constructor %s" c)

          | Some (i, (cname, _cty)) ->
              let b = oget (List.nth_opt bs i) in
              let cname = EcPath.pqoname (EcPath.prefix typ) cname in
              let tyinst = List.combine tydc.tyd_params tyinst in
              (e, ((typ, tyd, tyinst), cname), b)
        end

      | _ ->
          tc_error_lazy pf (fun fmt ->
            Format.fprintf fmt
              "the targetted instruction is not a match")
    in

    let f = form_of_expr m e in

    ((stmt head, subs, tail), (e, f), infos, cvars)

  let gen_rcond_full (pf, env) c me0 at_pos s =
    let m  = EcMemory.memory me0 in
    let (hd, s, tl), (e, f), ((typ, _tyd, tyinst), cname), cvars =
      gen_rcond (pf,env) c m at_pos s in

    let po1 =
      let names = List.map (
        fun (x, xty) ->
          let x =
            if   EcIdent.name x = "_"
            then EcIdent.create (symbol_of_ty xty)
            else EcIdent.fresh x
          in (x, xty)) cvars in
      let vars = List.map (curry f_local) names in
      let po = f_op cname (List.snd tyinst) f.f_ty in
      let po = f_app po vars f.f_ty in
      f_exists (List.map (snd_map gtty) names) (f_eq f po) in

    let me, pvs =
      let cvars =
        List.map
          (fun (x, xty) -> { v_name = EcIdent.name x; v_type = xty; })
          cvars in
      EcMemory.bindall_fresh cvars me0 in

    let subst, pvs =
      let s, pvs =
        List.fold_left_map (fun s ((x, xty), name) ->
            let pv = pv_loc name.v_name in
            let s  = Mid.add x (e_var pv xty) s in
            (s, (pv, xty)))
          Mid.empty (List.combine cvars pvs) in
      ({ e_subst_id with es_loc = s; }, pvs) in

    let frame =
      EcPV.PV.indep env
        (EcPV.e_read env e)
        (EcPV.PV.union (EcPV.s_read env hd) (EcPV.s_write env hd)) in

    (* If frame is false, we do not know how to create a cost. Use sp first. *)
    let epr, asgn, cost_opt =
    if frame then begin
      let vars = List.map (fun (pv, ty) -> f_pvar pv ty (fst me)) pvs in
      let epr = f_op cname (List.snd tyinst) f.f_ty in
      let epr = f_app epr vars f.f_ty in

      Some (f_eq f epr),
      [],
      Some (fun pre -> f_xadd (EcCHoare.cost_of_expr pre me e) f_x1)

    end else begin
      let asgn =
        EcModules.lv_of_list pvs |> omap (fun lv ->
          (* FIXME: factorize out *)
          let rty  = ttuple (List.snd cvars) in
          let proj = EcInductive.datatype_proj_path typ (EcPath.basename cname) in
          let proj = e_op proj (List.snd tyinst) (tfun e.e_ty (toption rty)) in
          let proj = e_app proj [e] (toption rty) in
          let proj = e_oget proj rty in
          i_asgn (lv, proj)) in

      None, otolist asgn, None
    end in

    (epr, hd, po1, cost_opt), (me, stmt (hd.s_node @ asgn @ (s_subst subst s).s_node @ tl))

  (* ------------------------------------------------------------------ *)
  let t_hoare_rcond_match_r c at_pos tc =
    let hs = tc1_as_hoareS tc in
    let (epr, hd, po1, _), (me, full) =
      gen_rcond_full (!!tc, FApi.tc1_env tc) c hs.hs_m at_pos hs.hs_s in

    let pr = ofold f_and hs.hs_pr epr in

    let concl1  = f_hoareS_r { hs with hs_s = hd; hs_po = po1; } in
    let concl2  = f_hoareS_r { hs with hs_pr = pr; hs_m = me; hs_s = full; } in

    FApi.xmutate1 tc `RCondMatch [concl1; concl2]

  (* ------------------------------------------------------------------ *)
  let t_bdhoare_rcond_match_r c at_pos tc =
    let bhs = tc1_as_bdhoareS tc in
    let (epr, hd, po1, _), (me, full) =
      gen_rcond_full (!!tc, FApi.tc1_env tc) c bhs.bhs_m at_pos bhs.bhs_s in

    let pr = ofold f_and bhs.bhs_pr epr in

    let concl1 = f_hoareS bhs.bhs_m bhs.bhs_pr hd po1 in
    let concl2 = f_bdHoareS_r { bhs with bhs_pr = pr; bhs_m = me; bhs_s = full; } in

    FApi.xmutate1 tc `RCondMatch [concl1; concl2]

  (* ------------------------------------------------------------------ *)
  let t_choare_rcond_match_r c at_pos tc =
    let chs = tc1_as_choareS tc in
    let (epr, hd, po1, cost_opt), (me, full) =
      gen_rcond_full (!!tc, FApi.tc1_env tc) c chs.chs_m at_pos chs.chs_s in

    match cost_opt with
    | None ->
      tc_error !!tc "choare match: the matched expression must be \
                     independent of the head statement (maybe use sp first?)."
    | Some lam_cost ->
      let cond, cost =
        EcCHoare.cost_sub_self chs.chs_co (lam_cost chs.chs_pr) in

      let pr = ofold f_and chs.chs_pr epr in

      let concl1 = f_hoareS chs.chs_m chs.chs_pr hd po1 in
      (* [full] must not contain any new assignments here! *)
      let concl2 = f_cHoareS_r { chs with chs_pr = pr;
                                          chs_m = me;
                                          chs_s = full;
                                          chs_co = cost} in

      FApi.xmutate1 tc `RCondMatch [concl1; cond; concl2]

  (* ------------------------------------------------------------------ *)
  let t_equiv_rcond_match_r side c at_pos tc =
    let es = tc1_as_equivS tc in

    let m, mo, s =
      match side with
      | `Left  -> es.es_ml, es.es_mr, es.es_sl
      | `Right -> es.es_mr, es.es_ml, es.es_sr in

    let (epr, hd, po1, _), (me, full) =
      gen_rcond_full (!!tc, FApi.tc1_env tc) c (EcFol.mhr, snd m) at_pos s in

    let mo'  = EcIdent.create "&m" in
    let s1   = Fsubst.f_subst_id in
    let s1   = Fsubst.f_bind_mem s1 (EcMemory.memory m) EcFol.mhr in
    let s1   = Fsubst.f_bind_mem s1 (EcMemory.memory mo) mo' in
    let pre1 = Fsubst.f_subst s1 es.es_pr in

    let epr  = omap (fun epr ->
      let se = Fsubst.f_subst_id in
      let se = Fsubst.f_bind_mem se EcFol.mhr (EcMemory.memory m)  in
      Fsubst.f_subst se epr) epr in

    let concl1 =
      f_forall_mems [mo', EcMemory.memtype mo]
        (f_hoareS (EcFol.mhr, EcMemory.memtype m) pre1 hd po1) in

    let (ml, mr), (sl, sr) =
      match side with
      | `Left ->
          ((fst es.es_ml, snd me), es.es_mr),
          (full, es.es_sr)

      | `Right ->
          (es.es_ml, (fst es.es_mr, snd me)),
          (es.es_sl, full) in

    let concl2 =
      f_equivS_r { es with
        es_pr = ofold f_and es.es_pr epr;
        es_ml = ml; es_mr = mr; es_sl = sl; es_sr = sr } in
    FApi.xmutate1 tc `RCond [concl1; concl2]

  (* ------------------------------------------------------------------ *)
  let t_hoare_rcond_match =
    FApi.t_low2 "hoare-rcond-match" t_hoare_rcond_match_r

  let t_bdhoare_rcond_match =
    FApi.t_low2 "hoare-rcond-match" t_bdhoare_rcond_match_r

  let t_choare_rcond_match =
    FApi.t_low2 "hoare-rcond-match" t_choare_rcond_match_r

  let t_equiv_rcond_match =
    FApi.t_low3 "hoare-rcond-match" t_equiv_rcond_match_r
end

(* -------------------------------------------------------------------- *)
let t_rcond_match side c at_pos tc =
  let concl = FApi.tc1_goal tc in

  match side with
  | None when is_bdHoareS concl -> LowMatch.t_bdhoare_rcond_match c at_pos tc
  | None when is_cHoareS concl  -> LowMatch.t_choare_rcond_match c at_pos tc
  | None -> LowMatch.t_hoare_rcond_match c at_pos tc
  | Some side -> LowMatch.t_equiv_rcond_match side c at_pos tc
