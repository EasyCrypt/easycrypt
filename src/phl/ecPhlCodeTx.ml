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
let cfold_stmt ?(simplify=true) ?(full=true) (pf, hyps) (me: memenv) olen zpr =
  let env = LDecl.toenv hyps in

  let rec doit (olen: int option) (acc: instr list) (insts: instr list) : instr list =
    let (asgn, i, tl) =
      match insts with
      | ({ i_node = Sasgn (lv, e) } as i) :: tl -> begin
        let asgn =
          match lv with
          | LvVar (x, ty) -> [(x, ty, e)]
          | LvTuple xs -> begin
              match e.e_node with
              | Etuple es -> List.map2 (fun (x, ty) e -> (x, ty, e)) xs es
              | _ -> assert false
          end
        in
          (asgn, i, tl)
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
    List.iter
      (fun (_, _, e) ->
          if e_fv e <> Mid.empty || e_read env e <> PV.empty then
            tc_error pf "right-values are not closed expression")
      asgn;

    let asg = List.fold_left
                (fun pv (x, ty, _) -> EcPV.PV.add env x ty pv)
                EcPV.PV.empty asgn
    in

  
    let subst =
      List.fold_left
        (fun subst (x, _ty, e) ->  Mpv.add env x e subst)
        Mpv.empty asgn
    in

    
    let do_subst = Mpv.isubst env subst in
    let do_substs = Mpv.issubst env subst in

    (* TEST CODE REMOVE LATER *) 
    let simpl (inst: instr) : instr =
      match inst.i_node with
      | Sasgn (l, e) -> i_asgn (l, (expr_of_form (fst me) (EcReduction.simplify EcReduction.nodelta hyps (form_of_expr (fst me) e))))
      | _ -> inst
    in
    let do_simpl tl1 = if simplify then List.map simpl tl1 else tl1 in
    let i = if simplify then simpl i else i in
    (* TEST CODE REMOVE LATER *)

    
    let p inst = PV.indep env (i_write env inst) asg in
    match olen with
    | None -> let p inst = PV.indep env (i_write env inst) asg in
      let tl1, tl2 = EcUtils.List.takedrop_while p tl in
      let tl1 = tl1 |> do_substs |> do_simpl in
      begin match tl2 with
      | [] -> acc @ tl1 @ [i]
      | inst::tl2 -> let tl2 = (Mpv.isubst env subst inst)::tl2 in 
        doit None (acc @ tl1) tl2
      end
    
    | Some olen ->
      if List.length tl < olen then
        tc_error pf "expecting at least %d instructions after assignment" olen;
      let tl1, tl2 = List.takedrop olen tl in
      begin match (List.for_all p tl1) with
      | true -> 
        let tl1 = do_simpl @@ do_substs tl1 in
        acc @ tl1 @ [i] @ tl2
      | false -> 
        let tl11, tl12 = EcUtils.List.takedrop_while p tl1 in
        let tl1, tl2 = tl11, tl12 @ tl2 in
        let tl1 = do_simpl @@ do_substs tl1 in
        let olen_rem = olen - (List.length tl1 + 1) in
        doit (Some olen_rem) (acc @ tl1) @@ (do_subst (List.hd tl2))::(List.tl tl2)
      end

      (* might be superfluous FIXME *)
      (* if not (EcPV.PV.indep env wrs asg) then *)
        (* tc_error pf "cannot cfold non read-only local variables" *)
      (* else *) 
         
  in
  let insts = doit olen [] Zpr.(zpr.z_tail) in

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
  let cpos = EcTyping.trans_codepos (FApi.tc1_env tc) cpos in
  t_cfold side cpos olen tc

let process_kill (side, cpos, len) tc =
  let cpos = EcTyping.trans_codepos (FApi.tc1_env tc) cpos in
  t_kill side cpos len tc

let process_alias (side, cpos, id) tc =
  let cpos = EcTyping.trans_codepos (FApi.tc1_env tc) cpos in
  t_alias side cpos id tc

let process_set (side, cpos, fresh, id, e) tc =
  let e = TTC.tc1_process_Xhl_exp tc side None e in
  let cpos = EcTyping.trans_codepos (FApi.tc1_env tc) cpos in
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
let process_case ((side, pos) : side option * pcodepos) (tc : tcenv1) =
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

  let s = EcLowPhlGoal.tc1_get_stmt side tc in
  let pos = EcTyping.trans_codepos env pos in
  let goals, s = EcMatching.Zipper.map env pos change s in
  let concl = EcLowPhlGoal.hl_set_stmt side concl s in

  FApi.xmutate1 tc `ProcCase (goals @ [concl])


(* -------------------------------------------------------------------- *)
(*             Start of Code Cryogenic Vault:                           *)
(* -------------------------------------------------------------------- *)
let subst_array env (me: memenv) (insts) : memenv * instr list =
  let cache : (prog_var, prog_var array * ty) Map.t = Map.empty in

  let size_of_array (arr_e: expr) = match arr_e.e_ty.ty_node with
  | Tconstr (p, _) -> begin match (EcPath.toqsymbol p) with
    | ["Top"; "Array256"; _], _ -> Some 256
    | ["Top"; "Array32"; _], _ -> Some 32
    | _, "ipoly" -> Some 256
    | h,t -> Format.eprintf "Unknown array type %s@." (List.fold_right (fun a b -> a ^ "." ^ b) h t);
      assert false
    end
  | _ -> None
  in
  let is_arr_read (e: expr) : bool =
  match e.e_node with
  | Eop (p, _) -> begin 
    match (EcPath.toqsymbol p) with
    | _, "_.[_]" -> true
    | _ -> Format.eprintf "Unknown arr read %a@." (EcPrinting.pp_expr (EcPrinting.PPEnv.ofenv env)) e; false
  end 
  | _ -> false 
  in
  let is_arr_write (e: expr) : bool =
  match e.e_node with
  | Eop (p, _) -> begin 
    match (EcPath.toqsymbol p) with
    | _, "_.[_<-_]" -> true
    | _ -> Format.eprintf "Unknown arr write %a@." (EcPrinting.pp_expr (EcPrinting.PPEnv.ofenv env)) e; false
  end 
  | _ -> false 
  in
  
  let vars_of_array (arr_e : expr) : prog_var array option =
    let name_from_array (arr_e : expr) : string = 
      match arr_e.e_node with
      | Evar (PVloc v) -> v
      | _ -> assert false
    in
    let name = name_from_array arr_e in
    match size_of_array arr_e with
    | None -> assert false
    | Some size -> Some ( 
      Array.init size (fun i -> 
        pv_loc @@ name ^ "_" ^ (string_of_int i)))
  in
  let array_of_vars (ty:ty) (vars: prog_var array) : expr =
    let vars = Array.map (fun v -> e_var v ty) vars in
    let vars = Array.map (form_of_expr (fst me)) vars in
    let arr = Array.fold_left 
      (fun acc v -> EcTypesafeFol.f_app_safe env EcCoreLib.CI_List.p_cons [v; acc]) 
      (fop_empty ty)
      (Array.rev vars)
    in 
    let () = Format.eprintf "type of list :%a @." (EcPrinting.pp_type (EcPrinting.PPEnv.ofenv env)) arr.f_ty in
    let p_of_list, o_of_list = EcEnv.Op.lookup (["Array" ^ (string_of_int @@ Array.length vars)], "of_list") env in
    let arr = EcTypesafeFol.f_app_safe env p_of_list [Array.get vars 0; arr] in
    let () = Format.eprintf "type of arr :%a @." (EcPrinting.pp_type (EcPrinting.PPEnv.ofenv env)) arr.f_ty in
    expr_of_form (fst me) arr

  in
  let rec subst_expr cache (e: expr) =
  match e.e_node with
  | Eapp (op, [{e_node=Evar arr_v} as arr_e; {e_node=Eint idx}]) when is_arr_read op -> 
    begin match Map.find_opt arr_v cache with
    | Some (vars, ty) -> (cache, e_var (Array.get vars (BI.to_int idx)) e.e_ty) 
    | None -> let vars = vars_of_array arr_e |> Option.get in
      (Map.add arr_v (vars, e.e_ty) cache, e_var (Array.get vars (BI.to_int idx)) e.e_ty)
    end
  | Eapp (op, args) -> let cache, args = List.fold_left_map (fun cache e -> subst_expr cache e) cache args in
    (cache, e_app op args e.e_ty)
  | _ -> (cache, e)
  in

  let subst_instr cache (i: instr) = 
  match i.i_node with
  | Sasgn (lv, e) -> begin match e.e_node with
    | Eapp (op, [{e_node=Evar arr_v} as arr_e; {e_node = Eint idx}; v]) 
      when is_arr_write op -> let cache, v = subst_expr cache v in
      let cache, var = match Map.find_opt arr_v cache with
      | Some (vars, ty) -> (cache, Array.get vars (BI.to_int idx))
      | None -> let vars = vars_of_array arr_e |> Option.get in
        (Map.add arr_v (vars, v.e_ty) cache, Array.get vars (BI.to_int idx)) in
      (cache, i_asgn (LvVar (var, v.e_ty), v))
    | Eapp _ -> let cache, e = subst_expr cache e in 
      (cache, i_asgn (lv, e))
    | _ -> (cache, i)
    end
  | _ -> (cache, i)
  in
  let cache, insts = List.fold_left_map subst_instr cache insts in
  let arr_defs = Map.to_seq cache 
    |> List.of_seq 
    |> List.map (fun (arr, (vars, ty)) -> i_asgn (LvVar (arr, ty), array_of_vars ty vars))
  in 
  let me = Map.fold (fun (vars, ty) me -> 
    let vars = Array.map (fun v -> match v with | PVloc v -> {ov_name = Some v; ov_type=ty} | _ -> assert false ) vars in
    EcMemory.bindall (Array.to_list vars) me) cache me in
  (me, insts @ arr_defs)
  
(* -------------------------------------------------------------------- *)
(*               End of Code Cryogenic Vault:                           *)
(* -------------------------------------------------------------------- *)
