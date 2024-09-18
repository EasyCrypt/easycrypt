(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcAst
open EcTypes
open EcModules
open EcFol
open EcEnv
open EcPV

open EcCoreGoal
open EcLowPhlGoal

module Mid = EcIdent.Mid
module Zpr = EcMatching.Zipper
module TTC = EcProofTyping
module Map = Batteries.Map

(* -------------------------------------------------------------------- *)
let t_kill_r side cpos olen tc =
  let env = FApi.tc1_env tc in

  let kill_stmt (pf, _) (_, po) me zpr =
    let (ks, tl) =
      match olen with
      | None -> (zpr.Zpr.z_tail, [])
      | Some len ->
          if List.length zpr.Zpr.z_tail < len then
            tc_error pf
              "cannot find %d consecutive instructions at given position"
              len;
          List.takedrop len zpr.Zpr.z_tail
    in

    (* FIXME [BG]: check the usage of po_rd *)
    let ks_wr = is_write env ks in
    let po_rd = PV.fv env (fst me) po in

    let pp_of_name =
      let ppe = EcPrinting.PPEnv.ofenv env in
        fun fmt x ->
          match x with
          | `Global p -> EcPrinting.pp_topmod ppe fmt p
          | `PV     p -> EcPrinting.pp_pv     ppe fmt p
    in

    List.iteri
      (fun i is ->
         let is_rd = is_read env is in
         let indp  = PV.interdep env ks_wr is_rd in
           match PV.pick indp with
           | None   -> ()
           | Some x ->
               match i with
               | 0 ->
                   tc_error !!tc
                     "code writes variables (%a) used by the current block"
                     pp_of_name x
               | _ ->
                   tc_error !!tc
                     "code writes variables (%a) used by the %dth parent block"
                     pp_of_name x i)
      (Zpr.after ~strict:false { zpr with Zpr.z_tail = tl; });

    begin
      match PV.pick (PV.interdep env ks_wr po_rd) with
      | None   -> ()
      | Some x ->
          tc_error !!tc
            "code writes variables (%a) used by the post-condition"
            pp_of_name x
    end;

    let kslconcl = EcFol.f_bdHoareS me f_true (stmt ks) f_true FHeq f_r1 in
      (me, { zpr with Zpr.z_tail = tl; }, [kslconcl])
  in

  let tr = fun side -> `Kill (side, cpos, olen) in
  t_code_transform side ~bdhoare:true cpos tr (t_zip kill_stmt) tc

(* -------------------------------------------------------------------- *)
let alias_stmt env id (pf, _) me i =
  let dopv ty =
    let id       = odfl "x" (omap EcLocation.unloc id) in
    let id       = { ov_name = Some id; ov_type = ty; } in
    let (me, id) = EcMemory.bind_fresh id me in
    (* oget cannot fail — Some in, Some out *)
    let pv       = pv_loc (oget id.ov_name)  in
    me, pv in

  match i.i_node with
  | Sasgn(lv,e) ->
    let ty = e.e_ty in
    let (me, pv) = dopv ty in
    (me, [i_asgn (LvVar (pv, ty), e); i_asgn (lv, e_var pv ty)])
  | Srnd (lv, e) ->
    let ty       = proj_distr_ty env e.e_ty in
    let (me, pv) = dopv ty in
    (me, [i_rnd (LvVar (pv, ty), e); i_asgn (lv, e_var pv ty)])
  | Scall (Some lv, f, args) ->
    let ty       = (EcEnv.Fun.by_xpath f env).f_sig.fs_ret in
    let (me, pv) = dopv ty in
    (me, [i_call (Some (LvVar (pv, ty)), f ,args); i_asgn (lv, e_var pv ty)])
  | _ ->
      tc_error pf "cannot create an alias for that kind of instruction"

let t_alias_r side cpos id g =
  let env = FApi.tc1_env g in
  let tr = fun side -> `Alias (side, cpos) in
  t_code_transform side ~bdhoare:true cpos tr (t_fold (alias_stmt env id)) g

(* -------------------------------------------------------------------- *)
let set_stmt (fresh, id) e =
  let get_i me =
    let id       = EcLocation.unloc id in
    let  v       = { ov_name = Some id; ov_type = e.e_ty } in
    let (me, id) = EcMemory.bind_fresh v me in
    (* oget cannot fail — Some in, Some out *)
    let pv       = pv_loc (oget id.ov_name) in

    (me, i_asgn (LvVar (pv, e.e_ty), e))
  in

  let get_i =
    if fresh then get_i
    else
      let res = ref None in
      fun me ->
        if !res = None then res := Some (get_i me);
        oget !res in
  fun _ _ me z ->
    let me,i = get_i me in
    (me, {z with Zpr.z_tail = i::z.Zpr.z_tail},[])

let t_set_r side cpos (fresh, id) e tc =
  let tr = fun side -> `Set (side, cpos) in
  t_code_transform side ~bdhoare:true cpos tr (t_zip (set_stmt (fresh, id) e)) tc

(* -------------------------------------------------------------------- *)
let cfold_stmt ?(simplify=true) (pf, hyps) (me: memenv) olen zpr =
  let env = LDecl.toenv hyps in

  (* Fold constant until next assignment or end of given # of lines *)
  let rec doit 
    ((asg, subst): PV.t * (expr,  unit) Mpv.t) 
    (olen: int option) 
    (acc: instr list) 
    (insts: instr list) 
    : instr list =
    let (asgn, tl) =
      match insts with
      | ({ i_node = Sasgn (lv, e) }) :: tl -> begin
        let asgn =
          match lv with
          | LvVar (x, ty) -> 
            (* check if first iteration or if variable is being propagated *)
            assert (asg = PV.empty || PV.mem_pv env x asg);
            [(x, ty, e)]
          | LvTuple xs -> begin
              match e.e_node with
              | Etuple es -> 
                (* check if first iteration or if all the variables in the tuple are being propagated *)
                assert (asg = PV.empty || 
                    List.for_all (fun x -> PV.mem_pv env x asg) (List.fst xs));
                List.map2 (fun (x, ty) e -> (x, ty, e)) xs es
              | _ -> assert false
          end
        in
          (asgn, tl)
      end

      | _ -> 
          tc_error pf "cannot find a left-value assignment at given position"
    in

    (* Check that we are assigning to local variables only *)
    List.iter
      (fun (x, _, _) ->
        if is_glob x then
          tc_error pf "left-values must be local variables")
      asgn;

    (* Check that we are assigning an expression that we can evaluate to a constant  *)
    let expr_is_closed (e: expr) : bool = Mid.is_empty (e_fv e) && PV.is_empty (e_read env e) in

    List.iter
      (fun (_, _, e) ->
          if not (expr_is_closed e) then
            tc_error pf "right-values are not closed expression")
      asgn;

    (* List of variables we are assigning to *)
    let asg = List.fold_left
                (fun pv (x, ty, _) -> EcPV.PV.add env x ty pv)
                asg asgn
    in

  
    let subst =
      List.fold_left
        (fun subst (x, _ty, e) ->  Mpv.add env x e subst)
        subst asgn
    in

    
    let do_subst = Mpv.isubst env subst in
    let do_substs = Mpv.issubst env subst in

    (* Rebuild assignments *)
    let asgn_instrs_from_pv_and_subst (asg) (subst) : instr = 
      let asgns = fst (PV.elements asg) in
      match asgns with 
      | [] -> assert false (* meaning we dont propagate, should never happen *)
      | [ (pv, ty) ] -> i_asgn (LvVar (pv, ty), e_var pv ty) |> (Mpv.isubst env subst)
      | xs -> i_asgn (LvTuple xs, e_tuple (List.map (fun (pv, ty) -> e_var pv ty) xs))
        |> (Mpv.isubst env subst)
    in
    let i = asgn_instrs_from_pv_and_subst asg subst in


    (* if flag set, simplify expression before assignment *)
    let simpl (inst: instr) : instr =
      match inst.i_node with
      | Sasgn (l, e) -> i_asgn (l, (expr_of_form (fst me) (EcReduction.simplify EcReduction.nodelta hyps (form_of_expr (fst me) e))))
      | _ -> inst
    in
    let do_simpl tl1 = if simplify then List.map simpl tl1 else tl1 in
    let i = if simplify then simpl i else i in
    
    let p inst = PV.indep env (i_write env inst) asg in
    match olen with
    (* If not len parameter, sub until end of prog or some folded var is set *)
    | None -> let p inst = PV.indep env (i_write env inst) asg in
      let tl1, tl2 = EcUtils.List.takedrop_while p tl in
      let tl1 = tl1 |> do_substs |> do_simpl in
      begin match tl2 with
      | inst :: tl2 -> let sinst = do_subst inst in 
        begin match sinst with 
        | {i_node = Sasgn (_, e)} when expr_is_closed e ->
          doit (asg, subst) None (acc @ tl1) (sinst :: tl2)
        | _ -> acc @ tl1 @ [i] @ (inst :: tl2) 
        end
      | [] -> acc @ tl1 @ [i]
      end
    
    | Some olen ->
      if List.length tl < olen then
        tc_error pf "expecting at least %d instructions after assignment" olen;
      let tl1, tl2 = List.takedrop olen tl in
      begin match (List.for_all p tl1) with
      (* Here we can fold the number we need *)
      | true -> 
        let tl1 = do_simpl @@ do_substs tl1 in
        acc @ tl1 @ [i] @ tl2
      (* Here we hit a write first so we recurse *)
      | false -> 
        let tl11, tl12 = EcUtils.List.takedrop_while p tl1 in
        let tl1, tl2 = tl11, tl12 @ tl2 in
        let tl1 = do_simpl @@ do_substs tl1 in
        let olen_rem = olen - (List.length tl1 + 1) in 
        begin match (List.hd tl2) with
        | {i_node = Sasgn (_lv, e)} ->
          if expr_is_closed e then
          doit (asg, subst) (Some olen_rem) (acc @ tl1) @@ (do_subst (List.hd tl2)) :: (List.tl tl2)
          else tc_error pf "non-closed assignment for propagated variable with %d lines remaining" olen_rem
        | _i -> tc_error pf "failed to propagate variable past non-assignment with %d lines remaining" olen_rem
        end
      end

  in
  let insts = doit (EcPV.PV.empty, Mpv.empty) olen [] Zpr.(zpr.z_tail) in

  let zpr =
    { zpr with Zpr.z_tail = insts }
  in
    (me, zpr, [])

let t_cfold_r side cpos olen g =
  let tr = fun side -> `Fold (side, cpos, olen) in
  let cb = fun cenv _ me zpr -> cfold_stmt cenv me olen zpr in
  t_code_transform side ~bdhoare:true cpos tr (t_zip cb) g

(* -------------------------------------------------------------------- *)
let t_kill  = FApi.t_low3 "code-tx-kill"  t_kill_r
let t_alias = FApi.t_low3 "code-tx-alias" t_alias_r
let t_set   = FApi.t_low4 "code-tx-set"   t_set_r
let t_cfold = FApi.t_low3 "code-tx-cfold" t_cfold_r

(* -------------------------------------------------------------------- *)
let process_cfold (side, cpos, olen) tc =
  t_cfold side cpos olen tc

let process_kill (side, cpos, len) tc =
  t_kill side cpos len tc

let process_alias (side, cpos, id) tc =
  t_alias side cpos id tc

let process_set (side, cpos, fresh, id, e) tc =
  let e = TTC.tc1_process_Xhl_exp tc side None e in
  t_set side cpos (fresh, id) e tc

(* -------------------------------------------------------------------- *)

let process_weakmem (side, id, params) tc =
  let open EcLocation in
  let hyps = FApi.tc1_hyps tc in
  let env = FApi.tc1_env tc in
  let _, f =
    try LDecl.hyp_by_name (unloc id) hyps
    with LDecl.LdeclError _ ->
      tc_lookup_error !!tc ~loc:id.pl_loc `Local ([], unloc id)
  in

  let process_decl (x, ty) =
    let ty = EcTyping.transty EcTyping.tp_tydecl env (EcUnify.UniEnv.create None) ty in
    let x = omap unloc (unloc x) in
    { ov_name = x; ov_type = ty }
  in

  let decls = List.map process_decl params in

  let bind me =
    try EcMemory.bindall decls me
    with EcMemory.DuplicatedMemoryBinding x ->
      tc_error ~loc:id.pl_loc !!tc "variable %s already declared" x in

  let h =
    match f.f_node with
    | FhoareS hs ->
      let me = bind hs.hs_m in
      f_hoareS_r { hs with hs_m = me }

    | FeHoareS hs ->
      let me = bind hs.ehs_m in
      f_eHoareS_r { hs with ehs_m = me }

    | FbdHoareS hs ->
      let me = bind hs.bhs_m in
      f_bdHoareS_r { hs with bhs_m = me }

    | FequivS es ->
      let do_side side es =
        let es_ml, es_mr = if side = `Left then bind es.es_ml, es.es_mr else es.es_ml, bind es.es_mr in
        {es with es_ml; es_mr}
      in
      let es =
        match side with
        | None -> do_side `Left (do_side `Right es)
        | Some side -> do_side side es in
      f_equivS_r es

    | _ ->
      tc_error ~loc:id.pl_loc !!tc
        "the hypothesis need to be a hoare/phoare/ehoare/equiv on statement"
  in
  let concl = f_imp h (FApi.tc1_goal tc) in
  FApi.xmutate1 tc `WeakenMem [concl]

(* -------------------------------------------------------------------- *)
let process_case ((side, pos) : side option * codepos) (tc : tcenv1) =
  let (env, _, concl) = FApi.tc1_eflat tc in

  let change (i : instr) =
    if not (is_asgn i) then
      tc_error !!tc "the code position should target an assignment";

    let lv, e = destr_asgn i in

    let pvl = EcPV.lp_write env lv in
    let pve = EcPV.e_read env e in
    let lv  = lv_to_list lv in

    if not (EcPV.PV.indep env pvl pve) then
      assert false;

    let e =
      match lv, e.e_node with
      | [_], _         -> [e]
      | _  , Etuple es -> es
      | _  ,_          -> assert false in

    let s = List.map2 (fun pv e -> i_asgn (LvVar (pv, e.e_ty), e)) lv e in

    ([], s)
  in

  let kinds = [`Hoare `Stmt; `EHoare `Stmt; `PHoare `Stmt; `Equiv `Stmt] in

  if not (EcLowPhlGoal.is_program_logic concl kinds) then
    assert false;

  let _, s = EcLowPhlGoal.tc1_get_stmt side tc in
  let goals, s = EcMatching.Zipper.map pos change s in
  let concl = EcLowPhlGoal.hl_set_stmt side concl s in

  FApi.xmutate1 tc `ProcCase (goals @ [concl])

