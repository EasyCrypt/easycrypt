(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcModules
open EcFol
open EcBaseLogic
open EcLogic
open EcCorePhl

(* -------------------------------------------------------------------- *)
module LowInternal = struct
  exception No_wp

  let wp_asgn_aux m lv e (lets,f) =
    let let1 = lv_subst m lv (form_of_expr m e) in
      (let1::lets, f)

  let rec wp_stmt onesided env m (stmt: EcModules.instr list) letsf =
    match stmt with
    | [] -> stmt, letsf
    | i :: stmt' ->
        try
          let letsf = wp_instr onesided env m i letsf in
            wp_stmt onesided env m stmt' letsf
        with No_wp -> (stmt, letsf)

  and wp_instr onesided env m i letsf =
    match i.i_node with
    | Sasgn (lv,e) ->
        wp_asgn_aux m lv e letsf

    | Sif (e,s1,s2) ->
        let r1,letsf1 = wp_stmt onesided env m (List.rev s1.s_node) letsf in
        let r2,letsf2 = wp_stmt onesided env m (List.rev s2.s_node) letsf in
        if r1=[] && r2=[] then
          let post1 = mk_let_of_lv_substs env letsf1 in
          let post2 = mk_let_of_lv_substs env letsf2 in
          let post  = f_if (form_of_expr m e) post1 post2 in
            ([], post)
        else raise No_wp

    | Sassert e when onesided ->
      let phi = form_of_expr m e in
      let (lets,f) = letsf in
      (lets,EcFol.f_and_simpl phi f)

    | _ -> raise No_wp
end

let wp ?(onesided=false) env m s post =
  let r,letsf = LowInternal.wp_stmt onesided env m (List.rev s.s_node) ([],post) in
    (List.rev r, mk_let_of_lv_substs env letsf)

(* -------------------------------------------------------------------- *)
class rn_hl_wp dp = object
  inherit xrule "[hl] wp"

  method doption : int doption = dp
end

let rn_hl_wp td = RN_xtd (new rn_hl_wp td :> xrule)

(* -------------------------------------------------------------------- *)
module TacInternal = struct
  let check_wp_progress msg i s remain =
    match i with
    | None -> List.length s.s_node - List.length remain
    | Some i ->
      match remain with
      | [] -> i
      | _  ->
        cannot_apply msg
          (Format.sprintf "remaining %i instruction(s)" (List.length remain))

  let t_hoare_wp i g =
    let env,_,concl = get_goal_e g in
    let hs = t_as_hoareS concl in
    let s_hd,s_wp = s_split_o "wp" i hs.hs_s in
    let s_wp,post =
      wp ~onesided:true env (EcMemory.memory hs.hs_m) (EcModules.stmt s_wp) hs.hs_po in
    let i = check_wp_progress "wp" i hs.hs_s s_wp in
    let s = EcModules.stmt (s_hd @ s_wp) in
    let concl = f_hoareS_r { hs with hs_s = s; hs_po = post} in
      prove_goal_by [concl] (rn_hl_wp (Single i)) g

  let t_bdHoare_wp i g =
    let env,_,concl = get_goal_e g in
    let bhs = t_as_bdHoareS concl in
    let s_hd,s_wp = s_split_o "wp" i bhs.bhs_s in
    let s_wp = EcModules.stmt s_wp in
    let m = EcMemory.memory bhs.bhs_m in
    let s_wp,post = wp env m s_wp bhs.bhs_po in
    let i = check_wp_progress "wp" i bhs.bhs_s s_wp in
    let s = EcModules.stmt (s_hd @ s_wp) in
    let concl = f_bdHoareS_r { bhs with bhs_s = s; bhs_po = post} in
      prove_goal_by [concl] (rn_hl_wp (Single i)) g

  let t_equiv_wp ij g =
    let env,_,concl = get_goal_e g in
    let es = t_as_equivS concl in
    let i = omap fst ij and j = omap snd ij in
    let s_hdl,s_wpl = s_split_o "wp" i es.es_sl in
    let s_hdr,s_wpr = s_split_o "wp" j es.es_sr in
    let s_wpl,post =
      wp env (EcMemory.memory es.es_ml) (EcModules.stmt s_wpl) es.es_po in
    let s_wpr, post =
      wp env (EcMemory.memory es.es_mr) (EcModules.stmt s_wpr) post in
    let i = check_wp_progress "wp" i es.es_sl s_wpl in
    let j = check_wp_progress "wp" j es.es_sr s_wpr in
    let sl = EcModules.stmt (s_hdl @ s_wpl) in
    let sr = EcModules.stmt (s_hdr @ s_wpr) in
    let concl = f_equivS_r {es with es_sl = sl; es_sr=sr; es_po = post} in
      prove_goal_by [concl] (rn_hl_wp (Double (i, j))) g
end

let t_wp k g =
  let module T = TacInternal in

  let (th, tbh, te) =
    match k with
    | None -> (Some (T.t_hoare_wp   None),
               Some (T.t_bdHoare_wp None),
               Some (T.t_equiv_wp   None))

    | Some (Single i) -> (Some (T.t_hoare_wp   (Some i)),
                          Some (T.t_bdHoare_wp (Some i)),
                          None (* ------------------- *))

    | Some (Double (i, j)) ->
        (None, None, Some (T.t_equiv_wp (Some (i, j))))

  in
    t_hS_or_bhS_or_eS ?th ?tbh ?te g
