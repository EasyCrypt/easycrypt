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
let cfold_stmt ?(simplify = true) (pf, hyps) (me : memenv) (olen : int option) (zpr : Zpr.zipper) =
  let env =  LDecl.toenv hyps in

  let simplify : expr -> expr =
    if simplify then (fun e ->
      let e = form_of_expr (fst me) e in
      let e = EcReduction.simplify EcReduction.nodelta hyps e in
      let e = expr_of_form (fst me) e in
      e
    ) else identity in

  let is_const_expression (e : expr) =
    PV.is_empty (e_read env e) in

  let for_instruction ((subst as subst0) : (expr, unit) Mpv.t) (i : instr) =
    let wr = EcPV.i_write env i in
    let i = Mpv.isubst env subst i in

    let (subst, asgn) =
      List.fold_left_map (fun subst ((pv, _) as pvty) ->
        match Mpv.find env pv subst with
        | e -> Mpv.remove env pv subst, Some (pvty, e)
        | exception Not_found -> subst, None
      ) subst (fst (PV.elements wr)) in

    let asgn = List.filter_map identity asgn in

    let mk_asgn (lve : ((prog_var * ty) * expr) list) =
      let lvs, es = List.split lve in
      lv_of_list lvs
      |> Option.map (fun lv -> i_asgn (lv, e_tuple es))
      |> Option.to_list in

    let exception Interrupt in

    try
      let subst, aout =
        let exception Default in

        try
          match i.i_node with
          | Sasgn (lv, e) ->
            (* We already removed the variables of `lv` from the substitution *)
            (* We are only interested in the variables of `lv` that are in `wr` *)
            let es =
              match simplify e, lv with
              | { e_node = Etuple es }, LvTuple _ -> es
              | _, LvTuple _ -> raise Default
              | e, _ -> [e] in

            let lv = lv_to_ty_list lv in
      
            let tosubst, asgn2 = List.partition (fun ((pv, _), e) ->
              Mpv.mem env pv subst0 && is_const_expression e
            ) (List.combine lv es) in
            
            let subst =
              List.fold_left
                (fun subst ((pv, _), e) -> Mpv.add env pv e subst)
                subst tosubst in

            let asgn =
              List.filter
                (fun ((pv, _), _) -> not (Mpv.mem env pv subst))
                asgn in

            (subst, mk_asgn asgn @ mk_asgn asgn2)

          | Srnd _ ->
            (subst, mk_asgn asgn @ [i])

          | _ -> raise Default

        with Default ->
          if List.exists
              (fun (pv, _) -> Mpv.mem env pv subst0)
              (fst (PV.elements wr))
          then raise Interrupt;
          (subst, mk_asgn asgn @ [i])

      in `Continue (subst, aout)

    with Interrupt -> `Interrupt
  in

  let body, epilog =
    match olen with
    | None ->
      (zpr.z_tail, [])
    | Some olen ->
      if List.length zpr.z_tail < olen+1 then
        tc_error pf "expecting at least %d instructions" olen;
      List.takedrop (olen+1) zpr.z_tail in

  let lv, subst, body, rem =
    match body with
    | { i_node = Sasgn (lv, e) } :: is ->
      let es =
        match simplify e, lv with
        | { e_node = Etuple es }, LvTuple _ -> es
        | _, LvTuple _ ->
            tc_error pf
              "the left-value is a tuple but the right-hand expression \
               is not a tuple expression";
        | e, _ -> [e] in
      let lv = lv_to_ty_list lv in

      if not (List.for_all is_const_expression es) then
        tc_error pf "right-values are not closed expressions";

      if not (List.for_all (is_loc |- fst) lv) then
        tc_error pf "left-values must be made of local variables only";

      let subst =
        List.fold_left
          (fun subst ((pv, _), e) -> Mpv.add env pv e subst)
          Mpv.empty (List.combine lv es) in

      let subst, is, rem =
        List.fold_left_map_while for_instruction subst is in

      lv, subst, List.flatten is, rem

    | _ ->
      tc_error pf "cannot find a left-value assignment at given position"
  in

  let lv, es =
    List.filter_map (fun ((pv, _) as pvty) ->
      match Mpv.find env pv subst with
      | e -> Some (pvty, e)
      | exception Not_found -> None
    ) lv |> List.split in

  let asgn =
    lv_of_list lv
    |> Option.map (fun lv -> i_asgn (lv, e_tuple es))
    |> Option.to_list in

  let zpr = { zpr with Zpr.z_tail = body @ asgn @ rem @ epilog } in
  (me, zpr, [])

(* -------------------------------------------------------------------- *)
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

