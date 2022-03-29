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

  let cost_of_expr_w_pre menv e c_pre = match c_pre with
    | None -> EcCHoare.cost_of_expr_any menv e
    | Some pre -> EcCHoare.cost_of_expr pre menv e

  let wp_asgn_aux c_pre memenv lv e (lets, f) =
    let m = EcMemory.memory memenv in
    let let1 = lv_subst ?c_pre m lv (form_of_expr m e) in
      (let1::lets, f)

  let rec wp_stmt
      onesided c_pre env memenv (stmt: EcModules.instr list) letsf cost =
    match stmt with
    | [] -> (stmt, letsf), cost
    | i :: stmt' ->
        try
          let letsf, i_cost = wp_instr onesided c_pre env memenv i letsf in
          wp_stmt
            onesided c_pre env memenv stmt' letsf (f_xadd cost i_cost)
        with No_wp -> (stmt, letsf), cost

  and wp_instr onesided c_pre env memenv i letsf =
    match i.i_node with
    | Sasgn (lv,e) ->
      wp_asgn_aux c_pre memenv lv e letsf, cost_of_expr_w_pre memenv e c_pre

    | Sif (e,s1,s2) ->
        let (r1,letsf1),cost_1 =
          wp_stmt onesided c_pre env memenv (List.rev s1.s_node) letsf f_x0 in
        let (r2,letsf2),cost_2 =
          wp_stmt onesided c_pre env memenv (List.rev s2.s_node) letsf f_x0 in
        if List.is_empty r1 && List.is_empty r2 then begin
          let post1 = mk_let_of_lv_substs env letsf1 in
          let post2 = mk_let_of_lv_substs env letsf2 in
          let m = EcMemory.memory memenv in
          let post  = f_if (form_of_expr m e) post1 post2 in
          let post  = f_and_simpl (odfl f_true c_pre) post in
          ([], post),
          f_xadd
            (f_xmax cost_1 cost_2)
            (cost_of_expr_w_pre memenv e c_pre)
        end else raise No_wp

    | Smatch (e, bs) -> begin
        let wps =
          let do1 (_, s) =
            wp_stmt onesided c_pre env memenv (List.rev s.s_node) letsf f_x0 in
          List.map do1 bs in

        if not (List.for_all (fun ((r, _), _) -> List.is_empty r) wps) then
          raise No_wp;
        let pbs =
          List.map2
            (fun (bds, _) ((_, letsf), _) ->
              let post = mk_let_of_lv_substs env letsf in
              f_lambda (List.map (snd_map gtty) bds) post)
            bs wps
        in
        let c =
          match wps with
          | [] -> f_x0
          | (_,c1) :: cs -> List.fold_left (fun c (_, c1) -> f_xmax c c1) c1 cs in
        let c = f_xadd c (cost_of_expr_w_pre memenv e c_pre) in
        let m = EcMemory.memory memenv in
        let post =
          f_and_simpl (odfl f_true c_pre) (f_match (form_of_expr m e) pbs EcTypes.tbool) in
        (([],post), c)
      end

    | Sassert e when onesided ->
        let phi = form_of_expr (EcMemory.memory memenv) e in
        let lets,f = letsf in
        (lets, EcFol.f_and_simpl phi f), cost_of_expr_w_pre memenv e c_pre

    | _ -> raise No_wp
end

let wp ?(uselet=true) ?(onesided=false) ?c_pre env m s post =
  let (r,letsf), cost =
    LowInternal.wp_stmt
      onesided c_pre env m (List.rev s.s_node)
      ([],post) f_x0
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

  let t_choare_wp ?(uselet=true) i c_pre tc =
    let env = FApi.tc1_env tc in
    EcCHoare.check_loaded env;
    let chs = tc1_as_choareS tc in

    let (s_hd, s_wp) = o_split i chs.chs_s in
    let s_wp = EcModules.stmt s_wp in

    let s_wp, post, cost_wp =
      wp ~uselet ~onesided:true ?c_pre env chs.chs_m s_wp chs.chs_po in
    check_wp_progress tc i chs.chs_s s_wp;
    let s = EcModules.stmt (s_hd @ s_wp) in
    let cond, cost = EcCHoare.cost_sub_self chs.chs_co cost_wp in
    let concl = f_cHoareS_r { chs with chs_s = s;
                                       chs_po = post;
                                       chs_co = cost } in
    FApi.xmutate1 tc `Wp [cond; concl]

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
let t_wp_r ?(uselet=true) ?cost_pre k g =
  let module T = TacInternal in

  let (th, tch, tbh, te) =
    match k with
    | None -> (Some (T.t_hoare_wp ~uselet None),
               Some (T.t_choare_wp  ~uselet None cost_pre),
               Some (T.t_bdhoare_wp ~uselet None),
               Some (T.t_equiv_wp   ~uselet None))

    | Some (Single i) -> (Some (T.t_hoare_wp   ~uselet (Some i)),
                          Some (T.t_choare_wp  ~uselet (Some i) cost_pre),
                          Some (T.t_bdhoare_wp ~uselet (Some i)),
                          None (* ------------------- *))

    | Some (Double (i, j)) ->
        (None, None, None, Some (T.t_equiv_wp ~uselet (Some (i, j)))) in

  let (th, tch, tbh, te) =
    match cost_pre with
    | None -> th, tch, tbh, te
    | Some _ ->
      let err tc =
        tc_error !!tc "cost precondition are only for choare judgement" in

      Some err, tch, Some err, Some err in

  t_hS_or_chS_or_bhS_or_eS ?th ?tch ?tbh ?te g

let t_wp ?(uselet=true) ?cost_pre = FApi.t_low1 "wp" (t_wp_r ~uselet ?cost_pre)

(* -------------------------------------------------------------------- *)
let typing_wp env m s f =
  match wp ~onesided:true env m s f with
  | [], f, _ -> Some f | _, _, _ -> None

let () = EcTyping.wp := Some typing_wp

(* -------------------------------------------------------------------- *)
let process_wp k cost_pre tc =
  let cost_pre  = match cost_pre with
    | Some pre -> Some (EcProofTyping.tc1_process_Xhl_formula tc pre)
    | None -> None in
  let t_after =
    match (FApi.tc1_goal tc).f_node with
    | FcHoareS _ -> [(fun x -> EcLowGoal.t_trivial x); EcLowGoal.t_id]
    | _          -> [ EcLowGoal.t_id] in
  FApi.t_seqsub (t_wp ?cost_pre k) t_after tc
