(* -------------------------------------------------------------------- *)
open EcUtils
open EcAst
open EcModules
open EcFol

open EcCoreGoal
open EcLowPhlGoal

(* -------------------------------------------------------------------- *)
module LowInternal = struct
  exception No_wp

  let wp_asgn_aux c_pre memenv lv e (lets, f) =
    let m = EcMemory.memory memenv in
    let let1 = lv_subst ?c_pre m lv (ss_inv_of_expr m e).inv in
      (let1::lets, f)

  let rec wp_stmt ?mc
      onesided c_pre env memenv (stmt: EcModules.instr list) letsf
  =
    match stmt with
    | [] -> (stmt, letsf)
    | i :: stmt' ->
        try
          let letsf = wp_instr ?mc onesided c_pre env memenv i letsf in
          wp_stmt ?mc onesided c_pre env memenv stmt' letsf
        with No_wp -> (stmt, letsf)

  and wp_instr ?mc onesided c_pre env memenv i letsf =
    match i.i_node with
    | Sasgn (lv,e) ->
      wp_asgn_aux c_pre memenv lv e letsf

    | Sif (e,s1,s2) ->
        let (r1,letsf1) =
          wp_stmt ?mc onesided c_pre env memenv (List.rev s1.s_node) letsf in
        let (r2,letsf2) =
          wp_stmt ?mc onesided c_pre env memenv (List.rev s2.s_node) letsf in
        if List.is_empty r1 && List.is_empty r2 then begin
          let post1 = mk_let_of_lv_substs ?mc:mc env letsf1 in
          let post2 = mk_let_of_lv_substs ?mc:mc env letsf2 in
          let m = EcMemory.memory memenv in
          let post  = f_if (ss_inv_of_expr m e).inv post1 post2 in
          let post  = f_and_simpl (odfl f_true c_pre) post in
          ([], post)
        end else raise No_wp

    | Smatch (e, bs) -> begin
        let wps =
          let do1 (_, s) =
            wp_stmt ?mc onesided c_pre env memenv (List.rev s.s_node) letsf in
          List.map do1 bs
        in

        if not (List.for_all (fun (r, _) -> List.is_empty r) wps) then
          raise No_wp;
        let pbs =
          List.map2
            (fun (bds, _) (_, letsf) ->
              let post = mk_let_of_lv_substs env letsf in
              f_lambda (List.map (snd_map gtty) bds) post)
            bs wps
        in
        let m = EcMemory.memory memenv in
        let post =
          f_and_simpl
            (odfl f_true c_pre)
            (f_match (ss_inv_of_expr m e).inv pbs EcTypes.tbool) in
        ([],post)
      end

    | Sassert e when onesided ->
        let phi = ss_inv_of_expr (EcMemory.memory memenv) e in
        let lets, f = letsf in
        (lets, EcFol.f_and_simpl phi.inv f)

    | _ -> raise No_wp

  let rec ewp_stmt env (memenv:EcMemory.memenv) (stmt: EcModules.instr list) letspf =
    match stmt with
    | [] -> stmt, letspf
    | i :: stmt' ->
        try
          let letspf = ewp_instr env memenv i letspf in
          ewp_stmt env memenv stmt' letspf
        with No_wp -> (stmt, letspf)

    and ewp_instr env (memenv:EcMemory.memenv) i letspf =
      match i.i_node with
      | Sasgn (lv, e) ->
        wp_asgn_aux None memenv lv e letspf

      | Srnd(lv, distr) ->
        let (lets,f) = letspf in
        let ty_distr = proj_distr_ty env (EcTypes.e_ty distr) in
        let x_id = EcIdent.create (symbol_of_lv lv) in
        let x = f_local x_id ty_distr in
        let m = EcMemory.memory memenv in
        let distr = (EcFol.ss_inv_of_expr m distr).inv in
        let let1 = lv_subst ?c_pre:None m lv x in
        let lets = let1 :: lets in
        let f = mk_let_of_lv_substs env (lets,f) in
        let f = f_Ep ty_distr distr (f_lambda [(x_id,GTty ty_distr)] f) in
        ([], f)

      | Sif(e, s1, s2) ->
        let r1,(lets1,f1) = ewp_stmt env memenv (List.rev s1.s_node) letspf in
        let r2,(lets2,f2) = ewp_stmt env memenv (List.rev s2.s_node) letspf in
        if List.is_empty r1 && List.is_empty r2 then begin
          let f1 = mk_let_of_lv_substs env (lets1,f1) in
          let f2 = mk_let_of_lv_substs env (lets2,f2) in
          let m = EcMemory.memory memenv in
          let e = (ss_inv_of_expr m e).inv in
          let f = f_if e f1 f2 in
          ([], f)
        end else raise No_wp

      | _ -> raise No_wp

end

let wp ?mc ?(uselet=true) ?(onesided=false) ?c_pre env m s post =
  let (r, letsf) =
    LowInternal.wp_stmt ?mc
      onesided c_pre env m (List.rev s.s_node) ([], post)
  in
  let pre = mk_let_of_lv_substs ?mc ~uselet env letsf in
  List.rev r, pre

let ewp ?(uselet=true) env m s post =
  let r,(lets,f) = LowInternal.ewp_stmt env m (List.rev s.s_node) ([],post) in
  let pre = mk_let_of_lv_substs ~uselet env (lets,f) in
  (List.rev r, pre)

(* -------------------------------------------------------------------- *)
module TacInternal = struct
  let check_wp_progress tc i (_s : stmt) rm =
    if EcUtils.is_some i && not (List.is_empty rm) then
      tc_error !!tc "remaining %i instruction(s)" (List.length rm)

  let t_hoare_wp ?(uselet=true) i tc =
    let env = FApi.tc1_env tc in
    let hs = tc1_as_hoareS tc in
    let (s_hd, s_wp) = o_split env i hs.hs_s in
    let s_wp = EcModules.stmt s_wp in
    let s_wp, post =
      wp ~uselet ~onesided:true env hs.hs_m s_wp (hs_po hs).inv in
    check_wp_progress tc i hs.hs_s s_wp;
    let s = EcModules.stmt (s_hd @ s_wp) in
    let m = fst hs.hs_m in
    let concl = f_hoareS (snd hs.hs_m) (hs_pr hs) s {m;inv=post} in
    FApi.xmutate1 tc `Wp [concl]

  let t_ehoare_wp ?(uselet=true) i tc =
    let env = FApi.tc1_env tc in
    let hs = tc1_as_ehoareS tc in
    let (s_hd, s_wp) = o_split env i hs.ehs_s in
    let s_wp = EcModules.stmt s_wp in
    let (s_wp, post) = ewp ~uselet env hs.ehs_m s_wp (ehs_po hs).inv in
    check_wp_progress tc i hs.ehs_s s_wp;
    let s = EcModules.stmt (s_hd @ s_wp) in
    let m = fst hs.ehs_m in
    let concl = f_eHoareS (snd hs.ehs_m) (ehs_pr hs) s {m;inv=post} in
    FApi.xmutate1 tc `Wp [concl]

  let t_bdhoare_wp ?(uselet=true) i tc =
    let env = FApi.tc1_env tc in
    let bhs = tc1_as_bdhoareS tc in
    let (s_hd, s_wp) = o_split env i bhs.bhs_s in
    let s_wp = EcModules.stmt s_wp in
    let s_wp,post = wp ~uselet env bhs.bhs_m s_wp (bhs_po bhs).inv in
    check_wp_progress tc i bhs.bhs_s s_wp;
    let s = EcModules.stmt (s_hd @ s_wp) in
    let m = fst bhs.bhs_m in
    let concl = f_bdHoareS (snd bhs.bhs_m) (bhs_pr bhs) s {m;inv=post} bhs.bhs_cmp (bhs_bd bhs) in
    FApi.xmutate1 tc `Wp [concl]

  let t_equiv_wp ?(uselet=true) ij tc =
    let env = FApi.tc1_env tc in
    let es = tc1_as_equivS tc in
    let ml, mr = (fst es.es_ml), (fst es.es_mr) in
    let i = omap fst ij and j = omap snd ij in
    let s_hdl,s_wpl = o_split env i es.es_sl in
    let s_hdr,s_wpr = o_split env j es.es_sr in
    let meml, s_wpl = es.es_ml, EcModules.stmt s_wpl in
    let memr, s_wpr = es.es_mr, EcModules.stmt s_wpr in
    let post = es_po es in
    let s_wpl, post = wp ~mc:(ml,mr) ~uselet env meml s_wpl post.inv in
    let s_wpr, post = wp ~mc:(ml,mr) ~uselet env memr s_wpr post in
    check_wp_progress tc i es.es_sl s_wpl;
    check_wp_progress tc j es.es_sr s_wpr;
    let sl = EcModules.stmt (s_hdl @ s_wpl) in
    let sr = EcModules.stmt (s_hdr @ s_wpr) in
    let concl = f_equivS (snd es.es_ml) (snd es.es_mr) (es_pr es) sl sr {ml;mr;inv=post} in
    FApi.xmutate1 tc `Wp [concl]
end

(* -------------------------------------------------------------------- *)
let t_wp_r ?(uselet=true) k g =
  let module T = TacInternal in

  let (th, teh, tbh, te) =
    match k with
    | None -> (Some (T.t_hoare_wp ~uselet None),
               Some (T.t_ehoare_wp  ~uselet None),
               Some (T.t_bdhoare_wp ~uselet None),
               Some (T.t_equiv_wp   ~uselet None))

    | Some (Single i) -> (Some (T.t_hoare_wp   ~uselet (Some i)),
                          Some (T.t_ehoare_wp  ~uselet (Some i)),
                          Some (T.t_bdhoare_wp ~uselet (Some i)),
                          None (* ------------------- *))

    | Some (Double (i, j)) ->
        (None, None, None, Some (T.t_equiv_wp ~uselet (Some (i, j)))) in

  t_hS_or_bhS_or_eS ?th ?teh ?tbh ?te g

let t_wp ?(uselet=true) = FApi.t_low1 "wp" (t_wp_r ~uselet)

(* -------------------------------------------------------------------- *)
let process_wp pos tc =
  let pos =
    Option.map (EcTyping.trans_dcodepos1 (FApi.tc1_env tc)) pos
  in t_wp pos tc
