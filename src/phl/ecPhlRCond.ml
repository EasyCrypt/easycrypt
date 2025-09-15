(* -------------------------------------------------------------------- *)
open EcUtils
open EcSymbols
open EcAst
open EcTypes
open EcDecl
open EcModules
open EcFol
open EcParsetree
open EcSubst

open EcCoreGoal
open EcLowPhlGoal

(* -------------------------------------------------------------------- *)
module Low = struct
  (* ------------------------------------------------------------------ *)
  let gen_rcond (pf, env) b m at_pos s =
    let head, i, tail = s_split_i env at_pos s in
    let e, s =
      match i.i_node with
      | Sif(e,s1,s2) -> e, if b then s1.s_node else s2.s_node
      | Swhile(e,s1) -> e, if b then s1.s_node@[i] else []
      | _ ->
          tc_error_lazy pf (fun fmt ->
            Format.fprintf fmt
              "the targetted instruction is not a conditionnal")
    in
    let f_e = ss_inv_of_expr m e in
    let f_e = if b then f_e else map_ss_inv1 f_not f_e in

    (stmt head, e, f_e, stmt (head @ s @ tail))

  (* ------------------------------------------------------------------ *)
  let t_hoare_rcond_r b at_pos tc =
    let env = FApi.tc1_env tc in
    let hs = tc1_as_hoareS tc in
    let m  = EcMemory.memory hs.hs_m in
    let hd,_,e,s = gen_rcond (!!tc, env) b m at_pos hs.hs_s in
    let concl1  = f_hoareS (snd hs.hs_m) (hs_pr hs) hd e in
    let concl2  = f_hoareS (snd hs.hs_m) (hs_pr hs) s (hs_po hs) in
    FApi.xmutate1 tc `RCond [concl1; concl2]

  (* ------------------------------------------------------------------ *)
  let t_ehoare_rcond_r b at_pos tc =
    let env = FApi.tc1_env tc in
    let hs = tc1_as_ehoareS tc in
    let m  = EcMemory.memory hs.ehs_m in
    let hd,_,e,s = gen_rcond (!!tc, env) b m at_pos hs.ehs_s in
    let pre pr =
      match destr_app pr with
      | o, pre :: _ when f_equal o fop_interp_ehoare_form -> pre
      | _ -> tc_error !!tc "the pre should have the form \"_ `|` _\"" in
    let pre = map_ss_inv1 pre (ehs_pr hs) in

    let concl1  = f_hoareS (snd hs.ehs_m) pre hd e in
    let concl2  = f_eHoareS (snd hs.ehs_m) (ehs_pr hs) s (ehs_po hs) in
    FApi.xmutate1 tc `RCond [concl1; concl2]

  (* ------------------------------------------------------------------ *)
  let t_bdhoare_rcond_r b at_pos tc =
    let env = FApi.tc1_env tc in
    let bhs = tc1_as_bdhoareS tc in
    let m  = EcMemory.memory bhs.bhs_m in
    let hd,_,e,s = gen_rcond (!!tc, env) b m at_pos bhs.bhs_s in
    let concl1  = f_hoareS (snd bhs.bhs_m) (bhs_pr bhs) hd e in
    let concl2  = f_bdHoareS (snd bhs.bhs_m) (bhs_pr bhs) s (bhs_po bhs) bhs.bhs_cmp (bhs_bd bhs) in
    FApi.xmutate1 tc `RCond [concl1; concl2]

  (* ------------------------------------------------------------------ *)
  let t_equiv_rcond_r side b at_pos tc =
    let env = FApi.tc1_env tc in
    let es = tc1_as_equivS tc in
    let m,mo,s =
      match side with
      | `Left  -> es.es_ml,es.es_mr, es.es_sl
      | `Right -> es.es_mr,es.es_ml, es.es_sr in
    let ts_inv_lower_side2 = sideif side ts_inv_lower_left2 ts_inv_lower_right2 in
    let ss_inv_generalize_other = sideif side ss_inv_generalize_right ss_inv_generalize_left in
    let hd,_,e,s = gen_rcond (!!tc, env) b (fst m) at_pos s in
    let e = ss_inv_generalize_other e (fst mo) in
    let concl1 = 
      EcSubst.f_forall_mems_ss_inv (EcIdent.create "&m", snd mo)
        (ts_inv_lower_side2 (fun pr po ->
          let mhs = EcIdent.create "&hr" in
          let pr = ss_inv_rebind pr mhs in
          let po = ss_inv_rebind po mhs in
          f_hoareS (snd m) pr hd po) (es_pr es) e) in
    let sl,sr = match side with `Left -> s, es.es_sr | `Right -> es.es_sl, s in
    let concl2 = f_equivS (snd es.es_ml) (snd es.es_mr) (es_pr es) sl sr (es_po es) in
    FApi.xmutate1 tc `RCond [concl1; concl2]

  (* ------------------------------------------------------------------ *)
  let t_hoare_rcond   = FApi.t_low2 "hoare-rcond"   t_hoare_rcond_r
  let t_ehoare_rcond  = FApi.t_low2 "ehoare-rcond"  t_ehoare_rcond_r
  let t_bdhoare_rcond = FApi.t_low2 "bdhoare-rcond" t_bdhoare_rcond_r
  let t_equiv_rcond   = FApi.t_low3 "equiv-rcond"   t_equiv_rcond_r
end

(* -------------------------------------------------------------------- *)
let t_rcond side b at_pos tc =
  let concl = FApi.tc1_goal tc in

  match side with
  | None when is_bdHoareS concl ->
    Low.t_bdhoare_rcond b at_pos tc
  | None when is_hoareS concl ->
    Low.t_hoare_rcond b at_pos tc
  | None ->
    Low.t_ehoare_rcond b at_pos tc
  | Some side ->
    Low.t_equiv_rcond side b at_pos tc

let process_rcond side b at_pos tc =
  let at_pos = EcProofTyping.tc1_process_codepos1 tc (side, at_pos) in
  t_rcond side b at_pos tc

(* -------------------------------------------------------------------- *)
module LowMatch = struct
  (* ------------------------------------------------------------------ *)
  let gen_rcond (pf, env) c m at_pos s =
    let head, i, tail = s_split_i env at_pos s in
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

    let f = ss_inv_of_expr m e in

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
      let cty = toarrow (List.snd names) f.inv.f_ty in
      let po = f_op cname (List.snd tyinst) cty in
      let po = f_app po vars f.inv.f_ty in
      map_ss_inv1 (f_exists (List.map (snd_map gtty) names)) (map_ss_inv2 f_eq f {m;inv=po}) in

    let me, pvs =
      let cvars =
        List.map
          (fun (x, xty) -> { ov_name = Some (EcIdent.name x); ov_type = xty; })
          cvars in
      EcMemory.bindall_fresh cvars me0 in

    let subst, pvs =
      let s = Fsubst.f_subst_id in
      let s, pvs =
        List.fold_left_map (fun s ((x, xty), name) ->
            let pv = pv_loc (oget name.ov_name) in
            let s  = bind_elocal s x (e_var pv xty) in
            (s, (pv, xty)))
          s (List.combine cvars pvs) in
      (s, pvs) in

    let frame =
      EcPV.PV.indep env
        (EcPV.e_read env e)
        (EcPV.PV.union (EcPV.s_read env hd) (EcPV.s_write env hd)) in

    let epr, asgn =
    if frame then begin
      let vars = List.map (fun (pv, ty) -> f_pvar pv ty (fst me)) pvs in
      let epr = f_op cname (List.snd tyinst) f.inv.f_ty in
      let epr = map_ss_inv ~m:f.m (fun vars -> f_app epr vars f.inv.f_ty) vars in
      Some (map_ss_inv2 f_eq f epr), []
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
      None, otolist asgn
    end in

    (epr, hd, po1), (me, stmt (hd.s_node @ asgn @ (s_subst subst s).s_node @ tl))

  (* ------------------------------------------------------------------ *)
  let t_hoare_rcond_match_r c at_pos tc =
    let hs = tc1_as_hoareS tc in
    let (epr, hd, po1), (me, full) =
      gen_rcond_full (!!tc, FApi.tc1_env tc) c hs.hs_m at_pos hs.hs_s in

    let pr = ofold (map_ss_inv2 f_and) (hs_pr hs) epr in

    let concl1  = f_hoareS (snd hs.hs_m) (hs_pr hs) hd po1 in
    let concl2  = f_hoareS (snd me) pr full (hs_po hs) in

    FApi.xmutate1 tc `RCondMatch [concl1; concl2]

  (* ------------------------------------------------------------------ *)
  let t_ehoare_rcond_match_r c at_pos tc =
    let hs = tc1_as_ehoareS tc in
    let (epr, hd, po1), (me, full) =
      gen_rcond_full (!!tc, FApi.tc1_env tc) c hs.ehs_m at_pos hs.ehs_s in

    let pr = ofold (map_ss_inv2 f_and) (ehs_pr hs) epr in

    let concl1  = f_eHoareS (snd hs.ehs_m) (ehs_pr hs) hd po1 in
    let concl2  = f_eHoareS (snd me) pr full (ehs_po hs) in

    FApi.xmutate1 tc `RCondMatch [concl1; concl2]

  (* ------------------------------------------------------------------ *)
  let t_bdhoare_rcond_match_r c at_pos tc =
    let bhs = tc1_as_bdhoareS tc in
    let (epr, hd, po1), (me, full) =
      gen_rcond_full (!!tc, FApi.tc1_env tc) c bhs.bhs_m at_pos bhs.bhs_s in

    let pr = ofold (map_ss_inv2 f_and) (bhs_pr bhs) epr in

    let concl1 = f_hoareS (snd bhs.bhs_m) (bhs_pr bhs) hd po1 in
    let concl2 = f_bdHoareS (snd me) pr full (bhs_po bhs) bhs.bhs_cmp (bhs_bd bhs) in

    FApi.xmutate1 tc `RCondMatch [concl1; concl2]

  (* ------------------------------------------------------------------ *)
  let t_equiv_rcond_match_r side c at_pos tc =
    let es = tc1_as_equivS tc in
    let ml, mr = fst es.es_ml, fst es.es_mr in

    let m, mo, s =
      match side with
      | `Left  -> es.es_ml, es.es_mr, es.es_sl
      | `Right -> es.es_mr, es.es_ml, es.es_sr in

    let (epr, hd, po1), (me, full) =
      gen_rcond_full (!!tc, FApi.tc1_env tc) c m at_pos s in

    let ss_inv_generalize_other inv = sideif side 
      (ss_inv_generalize_right inv mr) (ss_inv_generalize_left inv ml) in

    let epr  = omap (fun epr ->
      ss_inv_generalize_other (ss_inv_rebind epr (fst m))) epr in
    
    let ts_inv_lower_side1 =
      sideif side ts_inv_lower_left1 ts_inv_lower_right1 in

    let concl1 =
      f_forall_mems_ss_inv mo
        (ts_inv_lower_side1 (fun pr -> f_hoareS (snd m) pr hd po1) (es_pr es)) in

    let (ml, mr), (sl, sr) =
      match side with
      | `Left ->
          ((fst es.es_ml, snd me), es.es_mr),
          (full, es.es_sr)

      | `Right ->
          (es.es_ml, (fst es.es_mr, snd me)),
          (es.es_sl, full) in

    let concl2 =
      f_equivS (snd ml) (snd mr) (ofold (map_ts_inv2 f_and) (es_pr es) epr) sl sr (es_po es) in
    FApi.xmutate1 tc `RCond [concl1; concl2]

  (* ------------------------------------------------------------------ *)
  let t_hoare_rcond_match =
    FApi.t_low2 "hoare-rcond-match" t_hoare_rcond_match_r

  let t_ehoare_rcond_match =
    FApi.t_low2 "hoare-rcond-match" t_ehoare_rcond_match_r

  let t_bdhoare_rcond_match =
    FApi.t_low2 "hoare-rcond-match" t_bdhoare_rcond_match_r

  let t_equiv_rcond_match =
    FApi.t_low3 "hoare-rcond-match" t_equiv_rcond_match_r
end

(* -------------------------------------------------------------------- *)
let t_rcond_match side c at_pos tc =
  let concl = FApi.tc1_goal tc in

  match side with
  | None when is_bdHoareS concl -> LowMatch.t_bdhoare_rcond_match c at_pos tc
  | None when is_eHoareS concl -> LowMatch.t_ehoare_rcond_match c at_pos tc
  | None -> LowMatch.t_hoare_rcond_match c at_pos tc
  | Some side -> LowMatch.t_equiv_rcond_match side c at_pos tc

(* -------------------------------------------------------------------- *)
let process_rcond_match side c at_pos tc =
  let at_pos = EcProofTyping.tc1_process_codepos1 tc (side, at_pos) in
  t_rcond_match side c at_pos tc
