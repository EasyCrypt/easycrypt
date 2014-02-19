(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcPath
open EcTypes
open EcModules
open EcFol
open EcEnv
open EcBaseLogic
open EcLogic
open EcPV
open EcCorePhl
open EcCoreHiLogic

(* -------------------------------------------------------------------- *)
class rn_hl_fel cntr ash q fevent preds =
object
  inherit xrule "[hl] FEL"

  method cntr   : form = cntr
  method ash    : form = ash
  method q      : form = q
  method fevent : form = fevent
  method preds  : (xpath * form) list = preds
end

let rn_hl_fel cntr ash q fevent preds =
  RN_xtd (new rn_hl_fel cntr ash q fevent preds :> xrule)

(* -------------------------------------------------------------------- *)
let rec callable_oracles_f env modv os f =
  let f' = NormMp.norm_xfun env f in
  let func = Fun.by_xpath f' env in

  match func.f_def with
    | FBalias _ -> assert false (* normal form *)
    | FBabs oi ->
        let called_fs = 
          List.fold_left
            (fun s o -> 
              if PV.indep env modv (f_write env o) then s else EcPath.Sx.add o s)
            EcPath.Sx.empty oi.oi_calls
        in
        List.fold_left
          (callable_oracles_f env modv)
          os (EcPath.Sx.elements called_fs)
        
    | FBdef fdef ->
        let called_fs = 
          List.fold_left (fun s o -> 
            if PV.indep env modv (f_write env o) then s else EcPath.Sx.add o s)
            EcPath.Sx.empty fdef.f_uses.us_calls
        in
        let f_written = f_write ~except_fs:called_fs env f in
        if PV.indep env f_written modv then
          List.fold_left
            (callable_oracles_f env modv)
            os (EcPath.Sx.elements called_fs)
        else
          EcPath.Sx.add f os
          
and callable_oracles_s env modv os s =
  callable_oracles_is env modv os s.s_node

and callable_oracles_is env modv os is = 
  List.fold_left (callable_oracles_i env modv) os is

and callable_oracles_i env modv os i = 
  match i.i_node with
    | Scall(_,f,_) -> callable_oracles_f env modv os f
    | Sif (_,s1,s2) -> callable_oracles_s env modv (callable_oracles_s env modv os s1) s2
    | Swhile (_,s) -> callable_oracles_s env modv os s
    | Sasgn _ | Srnd _ | Sassert _ -> os 
    | Sabstract _ -> assert false (* FIXME *)

let callable_oracles_stmt env (modv:PV.t) = callable_oracles_s env modv EcPath.Sx.empty

(* -------------------------------------------------------------------- *)
let t_failure_event at_pos cntr ash q f_event pred_specs inv g =
  let env,_,concl = get_goal_e g in
  match concl.f_node with
    | Fapp ({f_node=Fop(op,_)},[pr;bd]) when is_pr pr 
        && EcPath.p_equal op EcCoreLib.p_real_le ->
      let (m,f,_args,ev) = destr_pr pr in
      let m = match Memory.byid m env with 
        | Some m -> m 
        | None -> cannot_apply "fel" "Cannot find memory (bug?)"
      in
      (* TODO B : did we have to subst more *)
      let memenv, (_,fdef), _env = 
        try Fun.hoareS f env
        with _ -> 
          cannot_apply "fel" "not applicable to abstract functions"
      in
      let s_hd,s_tl = s_split "fel" at_pos fdef.f_body in
      let fve = PV.fv env mhr f_event in
      let fvc = PV.fv env mhr cntr in
      let fv  = PV.union fve fvc in
      let os = callable_oracles_stmt env fv (stmt s_tl) in
      (* check that bad event is only modified in oracles *)
      let written_except_os = s_write ~except_fs:os env (stmt s_tl) in
      if not (PV.indep env written_except_os fv ) then
        tacuerror
          "fail event is modified outside oracles, ie: @. @[%a@] is not disjoint to @[%a@]@."
          (PV.pp env) written_except_os (PV.pp env) fv;
      (* subgoal on the bounds *)
      let bound_goal = 
        let intval = f_int_intval (f_int 0) (f_int_sub q (f_int 1)) in
        let v = f_int_sum ash intval treal in
        f_real_le v bd
      in
      (* we must quantify over memories *)
      let mo = EcIdent.create "&m" in
      let post_goal = 
        let subst = Fsubst.f_bind_mem Fsubst.f_subst_id mhr mo in
        let p = f_imp ev (f_and f_event (f_int_le cntr q)) in
        let p = Fsubst.f_subst subst p in
        f_forall_mems [mo, EcMemory.memtype m] p 
      in
      (* not fail and cntr=0 holds at designated program point *)
      let init_goal = 
        let p = f_and (f_not f_event) (f_eq cntr (f_int 0)) in
        let p = f_and_simpl p inv in
        f_hoareS memenv f_true (stmt s_hd) p
      in
      let oracle_goal o = 
        let not_F_to_F_goal = 
          let bound = f_app_simpl ash [cntr] treal in
          let pre = f_and (f_int_le (f_int 0) cntr) (f_not f_event) in
          let pre = f_and_simpl pre inv in
          let post = f_event in
          f_bdHoareF pre o post FHle bound
        in
        let old_cntr_id = EcIdent.create "c" in
        let old_b_id = EcIdent.create "b" in
        let old_cntr = f_local old_cntr_id tint in
        let old_b = f_local old_b_id tbool in
        let _,some_p = 
          try 
            List.find (fun (o',_) -> o=o') pred_specs 
          with Not_found ->
            (o, f_true)
        in
        let cntr_decr_goal = 
          let pre  = f_and some_p (f_eq old_cntr cntr) in
          let pre = f_and_simpl pre inv in
          let post = f_and (f_int_lt old_cntr cntr) (f_int_le cntr q) in
          let post = f_and_simpl post inv in
          f_forall_simpl [old_cntr_id,GTty tint] 
            (f_hoareF pre o post)
        in
        let cntr_stable_goal =
          let pre  = f_ands [f_not some_p;f_eq f_event old_b;f_eq cntr old_cntr] in
          let pre = f_and_simpl pre inv in
          let post = f_ands [f_eq f_event old_b;f_eq cntr old_cntr] in
          let post = f_and_simpl post inv in
          f_forall_simpl [old_b_id,GTty tbool; old_cntr_id,GTty tint] 
            (f_hoareF pre o post)
        in
        [not_F_to_F_goal;cntr_decr_goal;cntr_stable_goal]
      in
      let os_goals = List.concat (List.map oracle_goal (Sx.elements os)) in
      prove_goal_by ([bound_goal;post_goal;init_goal]@os_goals) 
        (rn_hl_fel cntr ash q f_event pred_specs)  g

    | _ -> 
      cannot_apply "failure event lemma" 
        "A goal of the form Pr[ _ ] <= _ was expected"
    
(* -------------------------------------------------------------------- *)
type pfel_t =
    pformula
  * pformula
  * pformula
  * pformula
  * (pgamepath * pformula) list
  * pformula option

let process_fel at_pos ((cntr, ash, q, f_event, pred_specs, o_inv) : pfel_t) g =
  let hyps,concl = get_goal g in

  (* code duplication from t_failure *)
  let f = match concl.f_node with
    | Fapp ({f_node=Fop(op,_)},[pr;_])
        when is_pr pr && EcPath.p_equal op EcCoreLib.p_real_le
      -> let (_,f,_,_) = destr_pr pr in f
    | _ -> 
      cannot_apply
        "failure event lemma" 
        "A goal of the form Pr[ _ ] <= _ was expected"
  in
  let hyps = fst (LDecl.hoareF f hyps) in 
  let cntr = process_form hyps cntr tint in
  let ash = process_form hyps ash (tfun tint treal) in
  let q = process_form hyps q tint in
  let f_event = process_form hyps f_event tbool in
  let inv =
    o_inv
      |> omap (fun inv -> process_form hyps inv tbool)
      |> odfl f_true
  in
  let process_pred (f,pre) = 
    let env = LDecl.toenv hyps in
    let f = EcTyping.trans_gamepath env f in
    let penv, _ = LDecl.hoareF f hyps in
      (f, process_form penv pre tbool)
  in
  let pred_specs = List.map process_pred pred_specs in
    t_failure_event at_pos cntr ash q f_event pred_specs inv g
