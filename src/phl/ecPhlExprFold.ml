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
  let range = cpos, `Offset (0, `ByPos (-1)) in
  let doit env si = 
    match si with
    | [] -> assert false
    | ai :: s when is_asgn ai ->
      let lv, e = destr_asgn ai in

      let pvs =
        List.fold_left
          (fun pvs (pv, t) -> PV.add env pv t pvs)
          PV.empty (lv_to_ty_list lv)
      in
      let evs = e_read env e in

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
        | i :: si when is_if i ->
          let writes = i_write env i in
          if PV.indep env writes pvs && PV.indep env writes evs then
            Mpv.isubst env subst i :: doit si
          else
            let e, t, f = destr_if i in
            let e = Mpv.esubst env subst e in
            let t = doit t.s_node in
            let f = doit f.s_node in
            i_if (e, stmt t, stmt f) :: si
        | i :: si when is_while i ->
          let writes = i_write env i in
          if PV.indep env writes pvs && PV.indep env writes evs then
            Mpv.isubst env subst i :: doit si
          else
            let e, t = destr_while i in
            let e = Mpv.esubst env subst e in
            let t = doit t.s_node in
            i_while (e, stmt t) :: si
        | i :: si when is_match i ->
          let writes = i_write env i in
          if PV.indep env writes pvs && PV.indep env writes evs then
            Mpv.isubst env subst i :: doit si
          else
            let e, bs = destr_match i in
            let e = Mpv.esubst env subst e in
            let bs = List.map (fun (bs, s) -> bs, stmt <| doit s.s_node) bs in
            i_match (e, bs) :: si
        | i :: si ->
          let writes = i_write env i in
          if PV.indep env writes pvs && PV.indep env writes evs then
            Mpv.isubst env subst i :: doit si
          else
            ai :: i :: si

      in
      doit s
    | _ -> failwith "Must be an assignment"
  in
  let s = Zipper.map_range env range doit s in
  let concl = hl_set_stmt oside (tc1_goal tc) s in
  xmutate1 tc `ExprFold [concl]

let process_efold (oside, pos) tc =
  let cp = EcProofTyping.tc1_process_codepos tc (oside, pos) in
  t_efold oside cp tc

  (*
let rec e_read e =
  match e.e_node with
  | Evar pv -> [pv]
  | _ -> EcTypes.e_fold (fun acc e -> acc @ e_read e) [] e

and i_read i =
  match i.i_node with
  | Sasgn (_, e)
  | Srnd (_, e) -> e_read e
  | Scall (_, _, es) -> List.concat_map e_read es
  | Swhile (e, t) -> (e_read e) @ (s_read t)
  | Sif (e, t, f) -> (e_read e) @ (s_read (s_seq t f))
  | Smatch (e, bs) ->
    e_read e @ List.concat_map (fun (_, s) -> s_read s) bs
  | _ -> []

and s_read s = List.concat_map i_read s.s_node

let rec split_to_first_write pv s =
  match s.s_node with
| [] -> [], []
  | i :: s -> begin
    let go =
      match i.i_node with
      | Sasgn (lv, _)
      | Scall (Some lv, _, _)
      | Srnd (lv, _) ->
        not (List.mem pv (lv_to_list lv))
      | Swhile (_, t) ->
        let _, tr = split_to_first_write pv t in
        tr = []
      | Sif (_, t, f) ->
        let _, tr = split_to_first_write pv t in
        let _, fr = split_to_first_write pv f in
        tr = [] && fr = []
      | Smatch (_, bs) ->
        let tails = List.map (fun (_, s) -> split_to_first_write pv s) bs in
        List.for_all (fun (_, t) -> t = []) tails
      | _ -> true
    in
    if go then
      let l, r = split_to_first_write pv (stmt s) in
      i :: l, r
    else
      [], i :: s
  end

let rec subst_assign simps keep_pvs s cutoff =
  match s with
  | [] -> s
  | i :: s when cutoff <> 0 -> begin
      match i.i_node with
      | Sasgn (LvVar (pv, _) as lv, e) ->
        let e = simps e in
        let subst = EcSubst.add_pv EcSubst.empty pv e in
        let pref, suff = split_to_first_write pv (stmt s) in
        let pref = EcSubst.subst_stmt subst (stmt pref) in

        (* Make sure to perform the substitution fully on the write instr *)
        let top =
          if suff = [] then
            None
          else
            let top = List.hd suff in
            match top.i_node with
            | Sasgn _ | Scall _ | Srnd _ ->
              Some (EcSubst.subst_stmt subst (stmt [top]))
            | Sif (e, t, f) ->
              let top = s_if ((EcSubst.subst_expr subst e), t, f) in
              Some top
            | Smatch (p, bs) ->
              let top = s_match ((EcSubst.subst_expr subst p), bs) in
              Some top
            | _ ->
              None
        in

        let s =
          match top with
          | None -> pref.s_node @ suff
          | Some i -> pref.s_node @ i.s_node @ (List.tl suff)
        in

        if suff <> [] || (List.mem pv keep_pvs) then
          let s = subst_assign simps (pv :: keep_pvs) s (cutoff - 1) in
          i_asgn (lv, e) :: s
        else
          subst_assign simps keep_pvs s (cutoff - 1)

      (* In the tuple case, just split things and defer to single lv case *)
      | Sasgn (LvTuple pvs, e) when EcTypes.is_tuple e ->
        let es = EcTypes.destr_tuple e in
        let new_assigns = List.map2 (fun pv e -> i_asgn (LvVar pv, e)) pvs es in
        subst_assign simps keep_pvs (new_assigns @ s) (cutoff + List.length new_assigns - 1) 

      | Sif (e, t, f) ->
        let e = simps e in
        let later_pvs = s_read (stmt s) in
        let t = subst_assign simps (later_pvs @ keep_pvs) t.s_node (-1) in
        let f = subst_assign simps (later_pvs @ keep_pvs) f.s_node (-1) in
        (i_if (e, stmt t, stmt f)) :: (subst_assign simps keep_pvs s (cutoff - 1))

      | Swhile (e, t) ->
        let e = simps e in
        let later_pvs = s_read (stmt s) in
        let t = subst_assign simps (later_pvs @ keep_pvs) t.s_node (-1) in
        (i_while (e, stmt t)) :: (subst_assign simps keep_pvs s (cutoff - 1))

      | Scall (olv, f, es) ->
        let es = List.map simps es in
        i_call (olv, f, es) :: (subst_assign simps keep_pvs s (cutoff - 1))

      | Srnd (lv, e) ->
        let e = simps e in
        i_rnd (lv, e) :: (subst_assign simps keep_pvs s (cutoff - 1))

      | _ -> i :: (subst_assign simps keep_pvs s (cutoff - 1))
  end
  | _ -> s

let prop_assigns simps s keep_pvs oregion = 
  let c_start, c_end = odfl (1, List.length s.s_node) oregion in
  let pref, suff = List.takedrop (c_start - 1) s.s_node in
  s_seq (stmt pref) (stmt (subst_assign simps keep_pvs suff (c_end - c_start + 1)))

let rec kill_branches s =
  match s.s_node with
  | [] -> s
  | i :: s -> begin
    match i.i_node with
    | Sif (e, t, f) -> begin
      match e.e_node with
      | Eop (p, _)
        when EcPath.p_equal p EcCoreLib.CI_Bool.p_true -> 
        kill_branches (s_seq t (stmt s))
      | Eop (p, _)
        when EcPath.p_equal p EcCoreLib.CI_Bool.p_false -> 
        kill_branches (s_seq f (stmt s))
      | _ -> s_seq (stmt [i]) (kill_branches (stmt s))
      end
    | _ -> s_seq (stmt [i]) (kill_branches (stmt s))
    end

let t_proc_simplify oside oregion tc =
  let hyps, concl = tc1_flat tc in
  let ri = EcReduction.nodelta in
  let change m (e : expr) =
    let f = EcFol.form_of_expr m e in
    let f = EcCallbyValue.norm_cbv ri hyps f in
    EcFol.expr_of_form m f
  in

  match oside, concl.f_node with
  | None, FhoareS _
  | Some `Left, FequivS _
  | Some `Right, FequivS _ ->
    let post = tc1_get_post tc in
    let m, s = tc1_get_stmt oside tc in
    let m = EcMemory.memory m in
    let post_pvs = EcFol.one_sided_pvs m post in
    let s = prop_assigns (change m) s post_pvs oregion in
    let s = kill_branches s in
    let concl = hl_set_stmt oside (tc1_goal tc) s in
    xmutate1 tc `ProcSimplify [concl]
  | None, FequivS es ->
    let ml = EcMemory.memory es.es_ml in
    let mr = EcMemory.memory es.es_mr in
    let post_pvs1 = EcFol.one_sided_pvs ml es.es_po in
    let post_pvs2 = EcFol.one_sided_pvs mr es.es_po in
    let s1 = prop_assigns (change ml) es.es_sl post_pvs1 oregion in
    let s1 = kill_branches s1 in
    let s2 = prop_assigns (change mr) es.es_sr post_pvs2 oregion in
    let s2 = kill_branches s2 in
    let concl = EcFol.f_equivS_r { es with es_sl = s1; es_sr = s2}in
    xmutate1 tc `ProcSimplify [concl]
  | _ -> tc_error !!tc "proc simplify is only valid for hoareS or equivS"
  *)
