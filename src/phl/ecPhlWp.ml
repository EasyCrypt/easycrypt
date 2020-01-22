(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcModules
open EcFol

open EcCoreGoal
open EcLowPhlGoal

(* -------------------------------------------------------------------- *)
module LowInternal = struct
  exception No_wp

  let wp_asgn_aux memenv lv e (lets, f) =
    let m = EcMemory.memory memenv in
    let let1 = lv_subst m lv (form_of_expr m e) in
      (let1::lets, f)

  let rec wp_stmt onesided env memenv (stmt: EcModules.instr list) letsf cost =
    match stmt with
    | [] -> (stmt, letsf), cost
    | i :: stmt' ->
        try
          let letsf, i_cost = wp_instr onesided env memenv i letsf in
          wp_stmt onesided env memenv stmt' letsf (f_int_add_simpl cost i_cost)
        with No_wp -> (stmt, letsf), cost

  and wp_instr onesided env memenv i letsf =
    match i.i_node with
    | Sasgn (lv,e) ->
      wp_asgn_aux memenv lv e letsf, cost_of_expr_any memenv e

    | Sif (e,s1,s2) ->
        let (r1,letsf1),cost_1 =
          wp_stmt onesided env memenv (List.rev s1.s_node) letsf f_i0 in
        let (r2,letsf2),cost_2 =
          wp_stmt onesided env memenv (List.rev s2.s_node) letsf f_i0 in
        if List.is_empty r1 && List.is_empty r2 then begin
          let post1 = mk_let_of_lv_substs env letsf1 in
          let post2 = mk_let_of_lv_substs env letsf2 in
          let m = EcMemory.memory memenv in
          let post  = f_if (form_of_expr m e) post1 post2 in
          ([], post),
          f_int_add_simpl cost_1
            (f_int_add_simpl cost_2 (cost_of_expr_any memenv e))
        end else raise No_wp

    | Sassert e when onesided ->
        let phi = form_of_expr (EcMemory.memory memenv) e in
        let lets,f = letsf in
        (lets, EcFol.f_and_simpl phi f), cost_of_expr_any memenv e

    | _ -> raise No_wp
end

let wp ?(uselet=true) ?(onesided=false) env m s post =
  let (r,letsf),cost =
    LowInternal.wp_stmt
      onesided env m (List.rev s.s_node)
      ([],post) f_i0
  in
  let pre = mk_let_of_lv_substs ~uselet env letsf in
  List.rev r, pre, cost

(* -------------------------------------------------------------------- *)
module TacInternal = struct
  let check_wp_progress tc i (_s : stmt) rm =
    if EcUtils.is_some i && not (List.is_empty rm) then
      tc_error !!tc "remaining %i instruction(s)" (List.length rm)

  let t_hoare_wp ?(uselet=true) i tc =
    let env = FApi.tc1_env tc in
    let hs = tc1_as_hoareS tc in
    let (s_hd, s_wp) = o_split i hs.hs_s in
    let s_wp = EcModules.stmt s_wp in
    let s_wp, post, _ =
      wp ~uselet ~onesided:true env hs.hs_m s_wp hs.hs_po in
    check_wp_progress tc i hs.hs_s s_wp;
    let s = EcModules.stmt (s_hd @ s_wp) in
    let concl = f_hoareS_r { hs with hs_s = s; hs_po = post} in
    FApi.xmutate1 tc `Wp [concl]

  let t_choare_wp ?(uselet=true) i tc =
    let env = FApi.tc1_env tc in
    let chs = tc1_as_choareS tc in
    let (s_hd, s_wp) = o_split i chs.chs_s in
    let s_wp = EcModules.stmt s_wp in
    let s_wp, post, cost_wp =
      wp ~uselet ~onesided:true env chs.chs_m s_wp chs.chs_po in
    check_wp_progress tc i chs.chs_s s_wp;
    let s = EcModules.stmt (s_hd @ s_wp) in
    let cost = cost_sub_self chs.chs_co cost_wp in
    let concl = f_cHoareS_r { chs with chs_s = s;
                                       chs_po = post;
                                       chs_co = cost } in
    FApi.xmutate1 tc `Wp [concl]

  let t_bdhoare_wp ?(uselet=true) i tc =
    let env = FApi.tc1_env tc in
    let bhs = tc1_as_bdhoareS tc in
    let (s_hd, s_wp) = o_split i bhs.bhs_s in
    let s_wp = EcModules.stmt s_wp in
    let s_wp,post,_ = wp ~uselet env bhs.bhs_m s_wp bhs.bhs_po in
    check_wp_progress tc i bhs.bhs_s s_wp;
    let s = EcModules.stmt (s_hd @ s_wp) in
    let concl = f_bdHoareS_r { bhs with bhs_s = s; bhs_po = post} in
    FApi.xmutate1 tc `Wp [concl]

  let t_equiv_wp ?(uselet=true) ij tc =
    let env = FApi.tc1_env tc in
    let es = tc1_as_equivS tc in
    let i = omap fst ij and j = omap snd ij in
    let s_hdl,s_wpl = o_split i es.es_sl in
    let s_hdr,s_wpr = o_split j es.es_sr in
    let meml, s_wpl = es.es_ml, EcModules.stmt s_wpl in
    let memr, s_wpr = es.es_mr, EcModules.stmt s_wpr in
    let post = es.es_po in
    let s_wpl, post, _ = wp ~uselet env meml s_wpl post in
    let s_wpr, post, _ = wp ~uselet env memr s_wpr post in
    check_wp_progress tc i es.es_sl s_wpl;
    check_wp_progress tc j es.es_sr s_wpr;
    let sl = EcModules.stmt (s_hdl @ s_wpl) in
    let sr = EcModules.stmt (s_hdr @ s_wpr) in
    let concl = f_equivS_r {es with es_sl = sl; es_sr=sr; es_po = post} in
    FApi.xmutate1 tc `Wp [concl]
end

(* -------------------------------------------------------------------- *)
let t_wp_r ?(uselet=true) k g =
  let module T = TacInternal in

  let (th, tch, tbh, te) =
    match k with
    | None -> (Some (T.t_hoare_wp   ~uselet None),
               Some (T.t_choare_wp  ~uselet None),
               Some (T.t_bdhoare_wp ~uselet None),
               Some (T.t_equiv_wp   ~uselet None))

    | Some (Single i) -> (Some (T.t_hoare_wp   ~uselet (Some i)),
                          Some (T.t_choare_wp  ~uselet (Some i)),
                          Some (T.t_bdhoare_wp ~uselet (Some i)),
                          None (* ------------------- *))

    | Some (Double (i, j)) ->
        (None, None, None, Some (T.t_equiv_wp ~uselet (Some (i, j))))

  in
    t_hS_or_chS_or_bhS_or_eS ?th ?tch ?tbh ?te g

let t_wp ?(uselet=true) = FApi.t_low1 "wp" (t_wp_r ~uselet)
