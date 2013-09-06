(* -------------------------------------------------------------------- *)
open EcUtils
open EcModules
open EcFol
open EcBaseLogic
open EcLogic
open EcCorePhl

(* -------------------------------------------------------------------- *)
class rn_hl_sp = object
  inherit xrule "[hl] SP"
end

let rn_hl_sp = RN_xtd (new rn_hl_sp :> xrule)

(* -------------------------------------------------------------------- *)
let rec sp_st side env mem pre (st : stmt) =
  List.fold_left
    (fun r i -> sp_inst side env mem r i.i_node)
    pre st.s_node

and sp_inst side env mem (pre : form) (inst : instr_node) : form =
  match inst with
  | Sasgn (LvVar (lf, lty) as lvL, muL) ->
      let fl   = f_pvar lf lty side in
      let x_id =
        if   EcIdent.id_equal mleft side
        then EcIdent.create (symbol_of_lv lvL ^ "L")
        else EcIdent.create (symbol_of_lv lvL ^ "R") in
      let x    = f_local x_id lty in
      let muL  = EcFol.form_of_expr (EcMemory.memory mem) muL in
      let muL' = (subst_form_lv env (EcMemory.memory mem) lvL x muL) in
      let fvl  = EcPV.PV.fv env (EcMemory.memory mem) pre in (* FV(pre) *)
      let fvm  = EcPV.PV.fv env (EcMemory.memory mem) muL in (* FV(e) *)
      if (EcPV.PV.mem_pv env lf fvl) || (EcPV.PV.mem_pv env lf fvm) then
        let pr = subst_form_lv env (EcMemory.memory mem) lvL x pre in
          f_exists [(x_id, GTty lty)] (f_and_simpl (f_eq fl muL') pr)
      else
        f_and_simpl (f_eq fl muL) pre

  | Sif (e, st1, st2) ->
      let b   = EcFol.form_of_expr (EcMemory.memory mem) e in
      let pb  = f_and_simpl pre b in
      let pnb = f_and_simpl pre (f_not b) in
      let sp1 = sp_st side env mem pb st1 in
      let sp2 = sp_st side env mem pnb st2 in
        f_or sp1 sp2

  | _ -> cannot_apply "sp" "instr. is not a single assignment or a conditional"

(* -------------------------------------------------------------------- *)
let t_sp_aux side g =
  let (env, _, concl) = get_goal_e g in
  let (stmt, m, menv, pre, prove_goal) =
    match concl.f_node with
    | FequivS es -> begin
        match side with
        | true ->
            let f pr st =
              let wes = f_equivS_r {es with es_sl=st; es_pr=pr} in
                t_on_last t_simplify_nodelta (prove_goal_by [wes] rn_hl_sp g)
            in
              (es.es_sl,mleft, es.es_ml, es.es_pr, f)

        | false ->
            let f pr st =
              let wes = f_equivS_r {es with es_sr=st; es_pr=pr} in
                t_on_last t_simplify_nodelta (prove_goal_by [wes] rn_hl_sp g)
            in
              (es.es_sr, mright, es.es_mr, es.es_pr, f)
    end

    | FhoareS hs ->
        let f pr st =
          let wes = f_hoareS_r {hs with hs_s=st; hs_pr=pr} in
            t_on_last t_simplify_nodelta (prove_goal_by [wes] rn_hl_sp g)
        in
          (hs.hs_s, mhr, hs.hs_m, hs.hs_pr, f)

    | FbdHoareS bhs ->
        let f pr st =
          let wes = f_bdHoareS_r {bhs with bhs_s=st; bhs_pr=pr} in
            t_on_last t_simplify_nodelta (prove_goal_by [wes] rn_hl_sp g)
        in
          (bhs.bhs_s, mhr, bhs.bhs_m, bhs.bhs_pr, f)

    | _ -> tacerror (NotPhl None)

  in let (pr, stmt) =
    let (l, ls) =
      match stmt.s_node with
      | []   -> cannot_apply "sp" "statement is empty"
      | i::s -> (i, EcModules.stmt s)
    in
    let pr  = sp_inst m env menv pre l.i_node in
      (pr, ls)
  in
    prove_goal pr stmt

(* -------------------------------------------------------------------- *)
let t_sp side g =
  let sp s = t_repeat (t_sp_aux s) in
    match side with
    | None   -> t_on_last (sp false) (sp true g)
    | Some s -> t_repeat  (t_sp_aux s) g
