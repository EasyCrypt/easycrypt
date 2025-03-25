open EcAst
open EcUtils

open EcCoreGoal.FApi
open EcLowPhlGoal

open EcMatching
open EcTypes
open EcFol
open EcModules

let e_true  = expr_of_form mhr f_true
let e_false = expr_of_form mhr f_false

let t_simp_all oside tc =
  let env = tc1_env tc in
  let _, s = tc1_get_stmt oside tc in
  let cps = Position.tag_codepos ~rev:true env s.s_node in
  let t = List.fold_right (fun (cp, _) t -> t_seq (t_try <| EcPhlRewrite.t_rewrite_simpl oside cp) t) cps EcLowGoal.t_id in
  t tc

let t_kill_branch oside cp tc =
  let env = tc1_env tc in
  let me, s = tc1_get_stmt oside tc in
  let doit i =
    match i.i_node with
    | Sif (e, t, _) when e = e_true ->
      me, t.s_node
    | Sif (e, _, f) when e = e_false ->
      me, f.s_node
    | Swhile (e, _) when e = e_false ->
      me, []
    | Smatch (e, bs) -> begin
      let ce, _ = EcTypes.split_args e in
      match ce.e_node with
      | Eop (p, _tys) ->
        let op = EcEnv.Op.by_path p env in
        if EcDecl.is_ctor op then
          let ctor, ix = EcDecl.operator_as_ctor op in
          let typ, tydc, tyinst = oget (EcEnv.Ty.get_top_decl e.e_ty env) in
          let tyinst = List.combine tydc.tyd_params tyinst in
          let locals, body = List.at bs ix in
          let cvars = List.map (fun (x, xty) -> { ov_name = Some (EcIdent.name x); ov_type = xty; }) locals in
          let me, cvars = EcMemory.bindall_fresh cvars me in

          let subst, pvs =
            let s = Fsubst.f_subst_id in
            let s, pvs = List.fold_left_map (fun s ((x, xty), name) ->
              let pv = pv_loc (oget name.ov_name) in
              let s  = bind_elocal s x (e_var pv xty) in
              (s, (pv, xty)))
            s (List.combine locals cvars)
            in
            (s, pvs)
          in
          let asgn = EcModules.lv_of_list pvs |> omap (fun lv ->
            let rty  = ttuple (List.snd locals) in
            let proj = EcInductive.datatype_proj_path typ (EcPath.basename ctor) in
            let proj = e_op proj (List.snd tyinst) (tfun e.e_ty (toption rty)) in
            let proj = e_app proj [e] (toption rty) in
            let proj = e_oget proj rty in
            i_asgn (lv, proj))
          in

          me, (match asgn with | None -> body.s_node | Some asgn -> asgn :: (Fsubst.s_subst subst body).s_node)
        else
          me, [i]
      | _ ->
        me, [i]
    end
    | _ -> me, [i]
  in
  let me, s = Zipper.map env cp doit s in
  let concl = hl_set_stmt_me oside (tc1_goal tc) s me in
  xmutate1 tc `KillBranches [concl]

let t_kill_branch_all oside tc =
  let env = tc1_env tc in
  let _, s = tc1_get_stmt oside tc in
  let cps = Position.tag_codepos ~rev:true env s.s_node in
  let cps_cond = List.filter (fun (_, i) -> is_if i || is_while i || is_match i) cps in
  let t = List.fold_right (fun (cp, _) t -> t_seq (t_try <| t_kill_branch oside cp) t) cps_cond EcLowGoal.t_id in
  t tc

let t_asgn_case_all oside tc =
  let env = tc1_env tc in
  let _, s = tc1_get_stmt oside tc in
  let cps = Position.tag_codepos ~rev:true env s.s_node in
  let cps_asgn = List.filter (fun (_, i) -> is_asgn i) cps in
  let t = List.fold_right (fun (cp, _) t -> t_seq (t_try <| EcPhlCodeTx.t_case (oside, cp)) t) cps_asgn EcLowGoal.t_id in
  t tc

let t_proc_crush oside tc =
  let rec doit tc max =
    let _, s = tc1_get_stmt oside tc in
    let tc = t_seq (t_asgn_case_all oside) (t_seq (EcPhlExprFold.t_efold_all oside) (t_seq (t_simp_all oside) (t_kill_branch_all oside))) tc in
    let tc1 = as_tcenv1 tc in
    let _, s' = tc1_get_stmt oside tc1 in
    if s = s' || max <= 0 then
      tc
    else
      doit tc1 (max - 1)
  in
  let env = tc1_env tc in
  let _, s = tc1_get_stmt oside tc in
  let cps = Position.tag_codepos ~rev:true env s.s_node in
  let cps_cond = List.filter (fun (_, i) -> is_if i || is_while i || is_match i) cps in
  doit tc (List.length cps_cond)
