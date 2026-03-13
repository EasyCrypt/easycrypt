(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcSymbols
open EcAst
open EcTypes
open EcModules
open EcFol
open EcEnv
open EcPV
open EcMatching

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
    let (m, mt) = me in
    let kslconcl = EcFol.f_bdHoareS mt {m;inv=f_true} (stmt ks) {m;inv=f_true} FHeq {m;inv=f_r1} in
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
let set_match_stmt (id : symbol) ((ue, mev, ptn) : _ * _ * form) =
  fun (pe, hyps) _ me z ->
    let i, is = List.destruct z.Zpr.z_tail in
    let e, mk =
      let e, kind, mk =
        get_expression_of_instruction i |> ofdfl (fun () ->
          tc_error pe "targetted instruction should contain an expression"
        ) in

      match kind with
      | `Sasgn | `Srnd | `Sif | `Smatch -> (e, mk)
      | `Swhile -> tc_error pe "while loops not supported"
    in

    try
      let ptev = EcProofTerm.ptenv pe hyps (ue, mev) in
      let e = ss_inv_of_expr (fst me) e in
      let subf, occmode = EcProofTerm.pf_find_occurence_lazy ptev ~ptn e.inv in
      let subf = {m=e.m; inv= subf} in

      assert (EcProofTerm.can_concretize ptev);

      let cpos =
        EcMatching.FPosition.select_form
          ~xconv:`AlphaEq ~keyed:occmode.k_keyed
          hyps None subf.inv e.inv in

      let v = { ov_name = Some id; ov_type = subf.inv.f_ty } in
      let (me, id) = EcMemory.bind_fresh v me in
      let pv = pv_loc (oget id.ov_name) in
      let e = map_ss_inv2 (fun pv -> EcMatching.FPosition.map cpos (fun _ -> pv)) (f_pvar pv (subf.inv.f_ty) (fst me)) e  in

      let i1 = i_asgn (LvVar (pv, subf.inv.f_ty), expr_of_ss_inv subf) in
      let i2 = mk (expr_of_ss_inv e) in

      (me, { z with z_tail = i1 :: i2 :: is }, [])

    with EcProofTerm.FindOccFailure _ ->
      tc_error pe "cannot find an occurrence of the pattern"

let t_set_match_r (side : oside) (cpos : Position.codepos) (id : symbol) pattern tc =
  let tr = fun side -> `SetMatch (side, cpos) in
  t_code_transform side ~bdhoare:true cpos tr
    (t_zip (set_match_stmt id pattern)) tc

(* -------------------------------------------------------------------- *)
let split_assignment (lv: lvalue) (e: expr) : ((prog_var * ty) * expr) list =
  match lv, e with
  | LvVar lv, e -> [(lv, e)]
  | LvTuple lvs, { e_node = Etuple es } ->
    List.combine lvs es
  | LvTuple lvs, e ->
    List.mapi (fun i (pv, ty) ->
      ((pv, ty), e_proj_simpl e i ty)) lvs


(*
  Works at the block level.
  Starts from the distinguished instruction given to it and does the following:
  Keep two sets:
  - propagate: set of variables to constant fold and propagate
  - preserve : set of variables whose value we need to preserve
  proceed through the instructions and do the following:
  - if instruction is an assignment:
    - if it is assigning to something in preserve:
      STOP
    - if it is assigning to something in propagate:
      update value of propagated variable, update preserve
      - preserve is now the set of variables read in the 
        assigning expression after propagation and simplification
    - otherwise:
      inline values of variables in propagate (and possibly simplify)
  - if instruction is control flow
  = this means (possibly not exhaustively) calls, whiles, ifs, matches
    - if no variables in propagate or preserve are written in the block:
      - propagate value to body and proceed
    - otherwise:
      STOP
  - if instruction is random sampling and variable is in propagate or preserve:
    STOP
  - when stopping:
    add assignments to the code for each of the values in propagate 
    setting them to the value they have in the substitution

  If eager:
    - we do not keep preserve and instead merge preserve into propagate.
    When encountering a variable we would need to preserve we add it 
    to the propagation set.
    - we can always keep going except for control flow
    = in the case of ifs we can also inline this (very eager mode?)
    = in the case of whiles it is very non-trivial how to do this automatically 
      (maybe not possible to do it fully automatically?)
    - for calls we could either inline (but should be done separately by the user)
      or we could use some contract that replaces a call by an assignment
      (should also be a separate tactic)
    - for random samplings we could continue but we can also stop

    - When hitting a stop condition we can do a partial stop as well:
      = throw out the variables that we cannot propagate and continue 
      with the rest

    TODO:
      Cfold n -> Cfold cpos_range
      Give propagate or preserve set to cfold?
*)

let cfold_stmt ?(simplify = true) ?(eager = true) (pf, hyps) (me : memenv) (olen : int option) (zpr : Zpr.zipper) =
  let env =  LDecl.toenv hyps in

  let e_simplify : expr -> expr =
    if simplify then (fun e ->
      let e = ss_inv_of_expr (fst me) e in
      let e = map_ss_inv1 (EcReduction.simplify EcReduction.nodelta hyps) e in
      let e = expr_of_ss_inv e in
      e
    ) else identity in

  let i_simplify : instr -> instr =
    if simplify then (fun i -> i) (* FIXME: get this to do something *)
    else identity
  in

  (* 
     for_instruction does the following:
       Check if you can propagate across the given instruction as per 
       description above
       If yes, do it, return the updates instructions (possibly none) 
       and update subst and preserve
       If STOP return Interrupt

     EAGER MODE:
      if we would fail by preserve ->
        add move preserve to propagate and push
      if we fail by if ->
        add if to subst
   *)
  let for_instruction (subst, preserve: (expr, unit) Mpv.t * (PV.t Mnpv.t)) (i : instr) =
    let esubst subst e = 
      EcPV.Mpv.esubst env subst e |> e_simplify
    in
    let isubst subst i =
      EcPV.Mpv.isubst env subst i |> i_simplify
    in
    let is_preserved preserve pv =
      Mnpv.exists (fun _ preserve -> EcPV.PV.mem_pv env pv preserve) preserve
    in
    let is_propagated subst pv =
      Mnpv.contains (Mpv.pvs subst) pv
    in
    let preserved_pvs preserve = 
      Mnpv.bindings preserve |> List.snd |> List.fold_left (PV.union) PV.empty
    in
    let propagated_pvs subst =
      (Mpv.pvs subst) |> Mnpv.bindings |> List.fst
    in
    let update_preserved preserve subst pv e =
      let rd = EcPV.e_read env e in
      let rd = List.fold_left (fun rd pv -> 
        EcPV.PV.remove env pv rd 
      ) rd (propagated_pvs subst) 
      in
      PVMap.add pv rd preserve
    in
    let promote_preserved_to_propagated subst preserve pv (e:expr) =
      let preserve = Mnpv.map (fun preserve ->
        PV.remove env pv preserve
      ) preserve
      in
      let subst = Mpv.add env pv e subst in
      (subst, preserve)
    in
    let collect_assignments asgns : instr option = 
      match asgns with
      | [] -> None
      | (lv, e)::[] -> Some (i_asgn ((LvVar lv), e))
      | asgns -> 
        let lvs, es = List.split asgns in
        let lv = LvTuple lvs in
        let e = e_tuple es in
        Some (i_asgn (lv, e))
    in
    match i.i_node with
    | Sasgn (lv, e) -> 
      let asgns = split_assignment lv e in
      let exception Abort in
      begin try 
        let (subst, preserve), asgns = List.fold_left_map (fun (subst, preserve) ((pv, t), e) ->
          if is_preserved preserve pv then 
            if eager 
            then 
              let e = esubst subst e in
              promote_preserved_to_propagated subst preserve pv e, None
            else raise Abort 
          else 
          if not (is_propagated subst pv) then 
            (subst, preserve), Some ((pv, t), esubst subst e)
          else 
            let e = esubst subst e in
            let rd = EcPV.e_read env e in
            (* We can propagate even if the expression
               depends on what is being assigned       
               FIXME: should we remove all variables
                      being propagated? 
            *)
            let rd = EcPV.PV.remove env pv rd in 
            (* FIXME: add case for eager *)
            let preserve = Mnpv.add pv rd preserve in 
            let subst = Mpv.add env pv e subst in
            (subst, preserve), None
        ) (subst, preserve) asgns
        in 
        let asgns = List.filter_map identity asgns in
        `Continue ((subst, preserve), Option.to_list (collect_assignments asgns))
        with Abort -> `Interrupt
      end
    | Srnd (_, _) 
    | Scall (_, _, _) 
    | Swhile (_, _) 
    | Sif (_, _, _) 
    | Smatch (_, _) -> 
      let wr = EcPV.i_write env i in
      let spvs = Mnpv.keys (Mpv.pvs subst) in
      let ppvs = Mnpv.keys preserve in
      if 
        let check = List.for_all (fun pv -> 
        not @@ EcPV.PV.mem_pv env pv wr) in
        check spvs && check ppvs
      then
        `Continue ((subst, preserve), [isubst subst i])
      else 
        `Interrupt
    | Sraise _ -> `Interrupt
    | Sabstract id -> 
      let aus = EcEnv.AbsStmt.byid id env in
      begin match aus with
      | { aus_calls = []; aus_reads; aus_writes } ->
        if List.for_all (fun (pv, _) ->
          not ((is_propagated subst pv) || (is_preserved preserve pv))
        ) (aus_reads @ aus_writes) then
          `Continue ((subst, preserve), [i])
        else
          `Interrupt
      | _ -> `Interrupt
      end
  in

  let body, epilog =
    match olen with
    | None ->
      (zpr.z_tail, [])
    | Some olen ->
      if List.length zpr.z_tail < olen+1 then
        tc_error pf "expecting at least %d instructions" olen;
      List.takedrop (olen+1) zpr.z_tail in

  let lv, (subst, preserve), body, rem =
    match body with
    | { i_node = Sasgn (lv, e) } :: is ->
      let asgns = split_assignment lv e in
      let lv = List.fst asgns in
      
      if not (List.for_all (is_loc -| fst) lv) then
        tc_error pf "left-values must be made of local variables only";

      (* Variables in the domain of substs 
         are variables to be propagated    *)
      let subst =
        List.fold_left
          (fun subst ((pv, _), e) -> Mpv.add env pv e subst)
          Mpv.empty asgns in

      let preserve = 
        List.fold_left 
          (fun preserve ((pv, _), e) -> 
            Mnpv.add 
              pv 
              EcPV.(PV.remove env pv (e_read env e))
              preserve)
          Mnpv.empty
          asgns
      in

      let (subst, preserve), is, rem =
        List.fold_left_map_while for_instruction (subst, preserve) is in

      lv, (subst, preserve), List.flatten is, rem

    | _ ->
      tc_error pf "cannot find a left-value assignment at given position"
  in

  Format.eprintf "Instructions folded:@.%a@." EcPrinting.(pp_stmt PPEnv.(ofenv env)) (stmt body);


  let asgns = Mnpv.bindings (Mpv.pvs subst) in 

  let lv, es = List.map (fun (pv, e) ->
    (pv, e_ty e), e) asgns |> List.split
  in

  let asgn =
    lv_of_list lv
    |> Option.map (fun lv -> i_asgn (lv, e_tuple es))
    |> Option.to_list in

  Format.eprintf "Cfold assignments:@.%a@." EcPrinting.(pp_stmt PPEnv.(ofenv env)) (stmt asgn);

  let zpr = { zpr with Zpr.z_tail = body @ asgn @ rem @ epilog } in
  (me, zpr, [])

(* -------------------------------------------------------------------- *)
let t_cfold_r side cpos olen eager g =
  let tr = fun side -> `Fold (side, cpos, olen) in
  let cb = fun cenv _ me zpr -> cfold_stmt ~eager cenv me olen zpr in
  t_code_transform side ~bdhoare:true cpos tr (t_zip cb) g

(* -------------------------------------------------------------------- *)
let t_kill      = FApi.t_low3 "code-tx-kill"      t_kill_r
let t_alias     = FApi.t_low3 "code-tx-alias"     t_alias_r
let t_set       = FApi.t_low4 "code-tx-set"       t_set_r
let t_set_match = FApi.t_low4 "code-tx-set-match" t_set_match_r
let t_cfold     = FApi.t_low4 "code-tx-cfold"     t_cfold_r

(* -------------------------------------------------------------------- *)
let process_cfold (side, cpos, olen, eager) tc =
  let cpos = EcLowPhlGoal.tc1_process_codepos tc (side, cpos) in
  t_cfold side cpos olen eager tc

let process_kill (side, cpos, len) tc =
  let cpos = EcLowPhlGoal.tc1_process_codepos tc (side, cpos) in
  t_kill side cpos len tc

let process_alias (side, cpos, id) tc =
  let cpos = EcLowPhlGoal.tc1_process_codepos tc (side, cpos) in
  t_alias side cpos id tc

let process_set (side, cpos, fresh, id, e) tc =
  let e = TTC.tc1_process_Xhl_exp tc side None e in
  let cpos = EcLowPhlGoal.tc1_process_codepos tc (side, cpos) in
  t_set side cpos (fresh, id) e tc

let process_set_match (side, cpos, id, pattern) tc =
  let cpos = EcLowPhlGoal.tc1_process_codepos tc (side, cpos) in
  let me, _ = tc1_get_stmt side tc in
  let hyps = LDecl.push_active_ss me (FApi.tc1_hyps tc) in
  let ue  = EcProofTyping.unienv_of_hyps hyps in
  let ptnmap = ref Mid.empty in
  let pattern = EcTyping.trans_pattern (LDecl.toenv hyps) ptnmap ue pattern in
  t_set_match side cpos (EcLocation.unloc id)
    (ue, EcMatching.MEV.of_idents (Mid.keys !ptnmap) `Form, pattern)
    tc

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
      let _, mt = bind hs.hs_m in
      f_hoareS mt (hs_pr hs) hs.hs_s (hs_po hs)

    | FeHoareS hs ->
      let _, mt = bind hs.ehs_m in
      f_eHoareS mt (ehs_pr hs) hs.ehs_s (ehs_po hs)

    | FbdHoareS hs ->
      let _, mt = bind hs.bhs_m in
      f_bdHoareS mt (bhs_pr hs) hs.bhs_s (bhs_po hs) hs.bhs_cmp (bhs_bd hs)

    | FequivS es ->
      let do_side side (ml, mr) =
        let es_ml, es_mr = if side = `Left then bind ml, mr else ml, bind mr in
        (es_ml, es_mr)
      in
      let ((_, mtl), (_, mtr)) =
        match side with
        | None -> do_side `Left (do_side `Right (es.es_ml, es.es_mr))
        | Some side -> do_side side (es.es_ml, es.es_mr) in
      f_equivS mtl mtr (es_pr es) es.es_sl es.es_sr (es_po es)

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

  let _, s = EcLowPhlGoal.tc1_get_stmt side tc in
  let pos = EcLowPhlGoal.tc1_process_codepos tc (side, pos) in
  let goals, s = EcMatching.Zipper.map env pos change s in
  let concl = EcLowPhlGoal.hl_set_stmt side concl s in

  FApi.xmutate1 tc `ProcCase (goals @ [concl])
