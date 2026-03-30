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
(*
  Works on a block starting at an assignment to local variables.

  It initializes:
  - propagate: a substitution mapping the assigned variables to their values
  - preserve : for each propagated variable, the variables that must keep their
    current value for that propagated expression to remain valid

  It then scans subsequent instructions from left to right.

  For assignments:
  - if the assigned variable is preserved, stop in non-eager mode; in eager
    mode, substitute in the right-hand side and promote that variable to the
    propagated substitution
  - if the assigned variable is already propagated, update its propagated value
    and recompute its preservation set
  - otherwise, substitute propagated values in the right-hand side and keep the
    assignment

  For calls, loops, conditionals, matches, and random samplings:
  - continue only if none of the currently propagated or preserved variables is
    written by the instruction; in that case, substitute propagated values in
    the instruction
  - otherwise, stop

  For abstract instructions without calls:
  - continue only if they neither read nor write propagated or preserved
    variables
  - otherwise, stop

  When the scan stops, the remaining propagated substitution is materialized as
  assignments appended after the transformed prefix.
*)

let cfold_stmt
  ?(simplify   : bool = true)
  ?(eager      : bool = true)
   ((pf, hyps) : proofenv * LDecl.hyps)
   (me         : memenv)
   (olen       : int option)
   (zpr        : Zpr.zipper)
=
  let env = LDecl.toenv hyps in

  let e_simplify (e : expr) =
    let e = form_of_expr ~m:(fst me) e in
    let e = EcReduction.simplify EcReduction.nodelta hyps e in
    expr_of_ss_inv { m = fst me; inv = e } in

  let i_simplify (i : instr) =
    i_map_expr e_simplify i in

  let e_simplify, i_simplify =
      if   simplify
      then (e_simplify, i_simplify)
      else (identity, identity) in

  (*
     Process one instruction under the current propagated substitution and
     preservation map.

     - `Continue ((subst, preserve), is)` means that propagation may proceed,
       with updated state and replacement instructions `is`
     - `Interrupt` means that propagation stops before this instruction

     In eager mode, assigning to a preserved variable does not stop the scan:
     the assigned expression is first substituted, then that variable is
     promoted into the propagated substitution.
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
    let propagated_pvs subst =
      (Mpv.pvs subst) |> Mnpv.bindings |> List.fst
    in
    (* Update preserve vars on assignment to given PV  *)
    (* Do not include any propagated vars, since these *)
    (* are automatically preserved by construction     *)
    let update_preserved preserve subst pv e =
      let rd = EcPV.e_read env e in
      let rd = List.fold_left (fun rd pv -> 
        EcPV.PV.remove env pv rd 
      ) rd (propagated_pvs subst) 
      in
      Mnpv.add pv rd preserve
    in
    let promote_preserved_to_propagated subst preserve pv (e:expr) =
      let preserve = Mnpv.map (fun preserve ->
        PV.remove env pv preserve
      ) preserve
      in
      let subst = Mpv.add env pv e subst in
      (subst, preserve)
    in

    match i.i_node with
    | Sasgn (lv, e) -> 
      let asgns = explode_assgn lv e in
      let exception Abort in
      begin try 
        let (subst, preserve), asgns = List.fold_left_map (fun (subst, preserve) ((pv, t), e) ->
          (* 1. When hitting an assignment to a preserved var *)
          if is_preserved preserve pv then 
            if eager (* 1.1 Promote to propagated on eager *)
            then 
              let e = esubst subst e in
              promote_preserved_to_propagated subst preserve pv e, None
            else raise Abort (* 1.2 Fail on non-eager *)
          else 
          (* 2. When not preserved and not propagated, do nothing *)
          if not (is_propagated subst pv) then 
            (subst, preserve), Some ((pv, t), esubst subst e)
          (* 3. When propagated, propagate *)
          else 
            let e = esubst subst e in
            let preserve = update_preserved preserve subst pv e in
            let subst = Mpv.add env pv e subst in
            (subst, preserve), None
        ) (subst, preserve) asgns
        in 
        let asgns = List.filter_map identity asgns in
        `Continue ((subst, preserve), Option.to_list (i_asgn_of_pve asgns))
        with Abort -> `Interrupt
      end

    | Srnd _ 
    | Scall _ 
    | Swhile _ 
    | Sif _ 
    | Smatch _ -> 
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

  let _lv, (subst, _preserve), body, rem =
    match body with
    | { i_node = Sasgn (lv, e) } :: is ->
      let asgns = explode_assgn lv e in
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

  let asgns = Mnpv.bindings (Mpv.pvs subst) in 

  let lv, es = List.map (fun (pv, e) ->
    (pv, e_ty e), e) asgns |> List.split
  in

  let asgn =
    lv_of_list lv
    |> Option.map (fun lv -> i_asgn (lv, e_tuple es))
    |> Option.to_list in

  let zpr =
    { zpr with Zpr.z_tail = body @ asgn @ rem @ epilog } in

  (me, zpr, [])

(* -------------------------------------------------------------------- *)
let t_cfold
  ~(eager : bool)
   (side  : side option)
   (cpos  : Position.codepos)
   (olen  : int option)
   (tc    : tcenv1)
=
    let tr = fun side -> `Fold (side, cpos, olen) in
    let cb = fun cenv _ me zpr -> cfold_stmt ~eager cenv me olen zpr in
    t_code_transform side ~bdhoare:true cpos tr (t_zip cb) tc 

(* -------------------------------------------------------------------- *)
let t_kill      = FApi.t_low3 "code-tx-kill"      t_kill_r
let t_alias     = FApi.t_low3 "code-tx-alias"     t_alias_r
let t_set       = FApi.t_low4 "code-tx-set"       t_set_r
let t_set_match = FApi.t_low4 "code-tx-set-match" t_set_match_r

(* -------------------------------------------------------------------- *)
let process_cfold (info : pcfold) tc =
  let cpos = EcLowPhlGoal.tc1_process_codepos tc (info.side, info.start) in
  t_cfold ~eager:info.eager info.side cpos info.length tc

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
