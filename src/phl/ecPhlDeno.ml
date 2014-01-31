(* -------------------------------------------------------------------- *)
open EcUtils
open EcTypes
open EcFol
open EcEnv
open EcBaseLogic
open EcLogic
open EcPV
open EcCorePhl
open EcCoreHiLogic

(* -------------------------------------------------------------------- *)
class rn_hl_deno = object
  inherit xrule "[hl] deno"
end

let rn_hl_deno = RN_xtd (new rn_hl_deno :> xrule)

(* -------------------------------------------------------------------- *)
let t_core_phoare_deno pre post g =
  let env,_,concl = get_goal_e g in
  let cmp, f, bd, concl_post =
    match concl.f_node with
    | Fapp({f_node = Fop(op,_)}, [f;bd]) when is_pr f &&
        EcPath.p_equal op EcCoreLib.p_real_le ->
      FHle, f, bd, fun ev -> f_imp_simpl ev post
    | Fapp({f_node = Fop(op,_)}, [f;bd]) when is_pr f &&
        EcPath.p_equal op EcCoreLib.p_eq ->
      FHeq, f, bd, f_iff_simpl post
    | Fapp({f_node = Fop(op,_)}, [bd;f]) when is_pr f &&
        EcPath.p_equal op EcCoreLib.p_real_le ->
      FHge, f, bd, f_imp_simpl post
    | _ -> cannot_apply "hoare_deno" "" (* FIXME error message *)
  in 
  let (m,f,args,ev) = destr_pr f in
  let concl_e = f_bdHoareF pre f post cmp bd in
  let fun_ = EcEnv.Fun.by_xpath f env in
  (* building the substitution for the pre *)
  let sargs = PVM.add env (pv_arg f) mhr args PVM.empty in
  let smem = Fsubst.f_bind_mem Fsubst.f_subst_id mhr m in
  let concl_pr  = Fsubst.f_subst smem (PVM.subst env sargs pre) in
  (* building the substitution for the post *)
  (* FIXME: *)
  (* let smem_ = Fsubst.f_bind_mem Fsubst.f_subst_id mhr mhr in  *)
  (* let ev   = Fsubst.f_subst smem_ ev in *)
  let me = EcEnv.Fun.actmem_post mhr f fun_ in
  let concl_po = f_forall_mems [me] (concl_post ev) in
    prove_goal_by [concl_e;concl_pr;concl_po] rn_hl_deno g  

let t_phoare_deno pre post g = 
  let concl = get_concl g in
  match concl.f_node with
  | Fapp({f_node = Fop(op,_)}, [bd;f]) when
      EcPath.p_equal op EcCoreLib.p_real_ge ->
    t_seq (t_apply_glob EcCoreLib.p_rle_ge_sym [] [AAform f;AAform bd; AAnode])
      (t_core_phoare_deno pre post) g
  | Fapp({f_node = Fop(op,_)}, [f;bd]) when
    EcPath.p_equal op EcCoreLib.p_eq && not (is_pr f) -> 
    t_seq t_symmetry (t_core_phoare_deno pre post) g
  | _ -> 
     t_core_phoare_deno pre post g

let t_equiv_deno pre post g =
  let env, _, concl = get_goal_e g in
  let cmp, f1, f2 =
    match concl.f_node with
    | Fapp({f_node = Fop(op,_)}, [f1;f2]) when is_pr f1 && is_pr f2 &&
        (EcPath.p_equal op EcCoreLib.p_eq || 
           EcPath.p_equal op EcCoreLib.p_real_le || 
           EcPath.p_equal op EcCoreLib.p_real_ge) ->
      let cmp = 
        if EcPath.p_equal op EcCoreLib.p_eq then `Eq
        else if EcPath.p_equal op EcCoreLib.p_real_le then `Le else `Ge in
      cmp, f1, f2
    | _ -> 
      cannot_apply "equiv_deno" "" in (* FIXME error message *)
  let (ml,fl,argsl,evl) = destr_pr f1 in
  let (mr,fr,argsr,evr) = destr_pr f2 in
  let concl_e = f_equivF pre fl fr post in
  let funl = EcEnv.Fun.by_xpath fl env in
  let funr = EcEnv.Fun.by_xpath fr env in
  (* building the substitution for the pre *)
  (* we should substitute param by args and left by ml and right by mr *)
  let sargs = PVM.add env (pv_arg fr) mright argsr PVM.empty in
  let sargs = PVM.add env (pv_arg fl) mleft argsl sargs in
  let smem = 
    Fsubst.f_bind_mem (Fsubst.f_bind_mem Fsubst.f_subst_id mright mr) mleft ml in
  let concl_pr  = Fsubst.f_subst smem (PVM.subst env sargs pre) in
  (* building the substitution for the post *)
  let smeml = Fsubst.f_bind_mem Fsubst.f_subst_id mhr mleft in 
  let smemr = Fsubst.f_bind_mem Fsubst.f_subst_id mhr mright in
  let evl   = Fsubst.f_subst smeml evl 
  and evr   = Fsubst.f_subst smemr evr in
  let cmp = 
    match cmp with 
    | `Eq -> f_iff evl evr 
    | `Le -> f_imp evl evr 
    | `Ge -> f_imp evr evl in 
  let mel = EcEnv.Fun.actmem_post mleft fl funl in
  let mer = EcEnv.Fun.actmem_post mright fr funr in
  let concl_po = f_forall_mems [mel;mer] (f_imp post cmp) in
    prove_goal_by [concl_e;concl_pr;concl_po] rn_hl_deno g  

(* -------------------------------------------------------------------- *)
(* FIXME: too much code repetition w.r.t. ecPhl (César) *)
let process_phoare_deno info (_,n as g) = 
  let process_cut g (pre,post) = 
    let hyps,concl = get_goal g in
    let error () = 
      tacuerror "the conclusion is not a suitable Pr expression" in
    let cmp, f, bd =
      match concl.f_node with
      | Fapp({f_node = Fop(op,_)}, [f1;f2]) when 
          EcPath.p_equal op EcCoreLib.p_eq ->
        if is_pr f1 then FHeq, f1, f2
        else if is_pr f2 then FHeq, f2, f1
        else error ()
      | Fapp({f_node = Fop(op,_)}, [f1;f2]) when 
          EcPath.p_equal op EcCoreLib.p_real_le ->
        if is_pr f1 then FHle, f1, f2 (* f1 <= f2 *)
        else if is_pr f2 then FHge, f2, f1 (* f2 >= f1 *)
        else error ()
      | Fapp({f_node = Fop(op,_)}, [f1;f2]) when 
          EcPath.p_equal op EcCoreLib.p_real_ge ->
        if is_pr f1 then FHge, f1, f2  (* f1 >= f2 *)
        else if is_pr f2 then FHle, f2, f1 (* f2 <= f1 *)
        else error ()
      | _ -> error () in
    let _,f,_,event = destr_pr f in
    let penv, qenv = LDecl.hoareF f hyps in
    let pre  = pre  |> omap_dfl (fun p -> process_form penv p tbool) f_true in
    let post = post |> omap_dfl (fun p -> process_form qenv p tbool) event in
    f_bdHoareF pre f post cmp bd 
  in
  let (juc,an), gs = process_mkn_apply (process_cut g) info g in
  let pre,post =
    let (_,f) = get_node (juc,an) in
    let bhf = t_as_bdHoareF f in
    bhf.bhf_pr, bhf.bhf_po
  in
    t_on_first (t_use an gs) (t_phoare_deno pre post (juc,n))

let process_equiv_deno info (_,n as g) = 
  let process_cut g (pre,post) = 
    let hyps,concl = get_goal g in
    let _op, f1, f2 =
      match concl.f_node with
      | Fapp({f_node = Fop(op,_)}, [f1;f2]) when is_pr f1 && is_pr f2 -> 
        op, f1, f2
      | _ ->  
        cannot_apply "bydeno" "" in (* FIXME error message *) 
    let _,fl,_,_ = destr_pr f1 in
    let _,fr,_,_ = destr_pr f2 in
    let penv, qenv = LDecl.equivF fl fr hyps in
    let pre  = pre |> omap_dfl (fun p -> process_form penv p tbool) f_true in
    (* FIXME: Benjamin : below: put a better default event instead of f_true *)
    let post = post |> omap_dfl (fun p -> process_form qenv p tbool) f_true in
    f_equivF pre fl fr post in
  let (juc,an), gs = process_mkn_apply (process_cut g) info g in
  let pre,post =
    let (_,f) = get_node (juc,an) in
    let ef = t_as_equivF f in
    ef.ef_pr, ef.ef_po
  in
    t_on_first (t_use an gs) (t_equiv_deno pre post (juc,n))

(* -------------------------------------------------------------------- *)
let process_deno mode info g =
  match mode with
  | `PHoare -> process_phoare_deno info g
  | `Equiv  -> process_equiv_deno  info g
