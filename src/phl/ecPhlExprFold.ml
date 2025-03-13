open EcAst
open EcUtils
open EcModules

open EcCoreGoal.FApi
open EcLowPhlGoal

open EcPV
open EcMatching

let t_efold oside cpos tc =
  let env = tc1_env tc in
  let _, s = tc1_get_stmt oside tc in
  let range = cpos, `Offset (1, `ByPos (-1)) in
  let doit env si =
    match si with
    | [] -> assert false
    | ai :: s when is_asgn ai ->
      let lv, e = destr_asgn ai in

      let evs = e_read env e in
      let pvs =
        List.fold_left
          (fun pvs (pv, t) -> PV.add env pv t pvs)
          PV.empty (lv_to_ty_list lv)
      in

      let can_forward_subst = PV.indep env evs pvs in
      let pvs = PV.union evs pvs in

      let pves =
        match lv, e.e_node with
        | LvTuple pvts, Etuple es ->
          List.combine (List.fst pvts) es
        | LvVar (pv, _), _ ->
          [pv, e]
        | LvTuple pvts, _ ->
          List.mapi (fun i (pv, t) -> pv, EcTypes.e_proj e i t) pvts
      in
      let subst = List.fold_left (fun subst (pv, e) -> Mpv.add env pv e subst) Mpv.empty pves in

      let rec doit si =
        match si with
        | [] -> [ai]
        | i :: si -> begin
          let writes = i_write env i in
          let reads = i_read env i in
          if (PV.indep env writes pvs && not (is_call i))
          || (PV.indep env (PV.union reads writes) pvs && is_call i) then
            Mpv.isubst env subst i :: doit si
          else
            match i.i_node with
            |Sif (e, t, f) ->
              let e = Mpv.esubst env subst e in
              let t = doit t.s_node in
              let f = doit f.s_node in
              i_if (e, stmt t, stmt f) :: si
            | Swhile (e, t) ->
              let e = Mpv.esubst env subst e in
              let t = doit t.s_node in
              i_while (e, stmt t) :: si
            | Smatch (e, bs) ->
              let e = Mpv.esubst env subst e in
              let bs = List.map (fun (bs, s) -> bs, stmt <| doit s.s_node) bs in
              i_match (e, bs) :: si
            | _ ->
              let i = if can_forward_subst then Mpv.isubst env subst i else i in
              ai :: i :: si
        end
      in
      doit s
    | _ -> failwith "Must be an assignment"
  in
  let s = Zipper.map_range env range doit s in
  let concl = hl_set_stmt oside (tc1_goal tc) s in
  xmutate1 tc `ExprFold [concl]

let t_efold_all oside tc =
  let env = tc1_env tc in
  let _, s = tc1_get_stmt oside tc in
  let cps = Position.tag_codepos ~rev:true env s.s_node in
  let cps_asgn = List.filter (fun (_, i) -> is_asgn i) cps in
  let t = List.fold_right (fun (cp, _) t -> t_seq (t_try <| t_efold oside cp) t) cps_asgn EcLowGoal.t_id in
  t tc

let process_efold (oside, pos) tc =
  match pos with
  | None ->
    t_efold_all oside tc
  | Some cp ->
    let cp = EcProofTyping.tc1_process_codepos tc (oside, cp) in
    t_efold oside cp tc
