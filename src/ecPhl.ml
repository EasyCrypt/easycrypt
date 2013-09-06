(* -------------------------------------------------------------------- *)
open EcParsetree
open EcUtils
open EcIdent
open EcPath
open EcCoreLib
open EcTypes
open EcFol
open EcBaseLogic
open EcEnv
open EcPV
open EcLogic
open EcModules
open EcMetaProg
open EcCorePhl

(* --------------------------------------------------------------------- *)
class rn_hl_hoare_equiv = object inherit xrule "[hl] hoare-equiv" end
let rn_hl_hoare_equiv = RN_xtd (new rn_hl_hoare_equiv)

let t_hoare_equiv p q p1 q1 p2 q2 g =
  let concl = get_concl g in
  let es = t_as_equivS concl in
  let s1 = Fsubst.f_bind_mem Fsubst.f_subst_id mhr (fst es.es_ml) in
  let s2 = Fsubst.f_bind_mem Fsubst.f_subst_id mhr (fst es.es_mr) in
  let concl1 = 
    f_forall_mems [es.es_ml;es.es_mr] 
      (f_imp es.es_pr (f_and p (f_and (Fsubst.f_subst s1 p1) (Fsubst.f_subst s2 p2)))) in
  let concl2 = 
    f_forall_mems [es.es_ml;es.es_mr]
      (f_imps [q;Fsubst.f_subst s1 q1;Fsubst.f_subst s2 q2] es.es_po) in
  let concl3 = 
    f_hoareS (mhr,snd es.es_ml) p1 es.es_sl q1 in
  let concl4 = 
    f_hoareS (mhr,snd es.es_mr) p2 es.es_sr q2 in
  let concl5 = 
    f_equivS_r { es with es_pr = p; es_po = q } in
  prove_goal_by [concl1; concl2; concl3; concl4; concl5] 
    rn_hl_hoare_equiv g

(*
let t_equiv_mod 
{P} c1 ~ c2 {Q}
P => forall mod, Q => Q' 
-------------------------
{P} c1 ~ c2 {Q'}
*)

(*
let t_equiv_true 
lossless c1
lossless c2
------------------
{P} c1 ~ c2 {true}

*)

(* -------------------------------------------------------------------- *)
class rn_hl_deno = object inherit xrule "[hl] deno" end
let rn_hl_deno = RN_xtd (new rn_hl_deno)

let t_bdHoare_deno pre post g =
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
        (EcPath.p_equal op EcCoreLib.p_eq) ->
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
  let sargs = 
    List.fold_left2 (fun s v a -> PVM.add env (pv_loc f v.v_name) mhr a s)
      PVM.empty fun_.f_sig.fs_params args in
  let smem = Fsubst.f_bind_mem Fsubst.f_subst_id mhr m in
  let concl_pr  = Fsubst.f_subst smem (PVM.subst env sargs pre) in
  (* building the substitution for the post *)
  (* FIXME: *)
  (* let smem_ = Fsubst.f_bind_mem Fsubst.f_subst_id mhr mhr in  *)
  (* let ev   = Fsubst.f_subst smem_ ev in *)
  let me = EcEnv.Fun.actmem_post mhr f fun_ in
  let concl_po = f_forall_mems [me] (concl_post ev) in
  prove_goal_by [concl_e;concl_pr;concl_po] rn_hl_deno g  

let t_equiv_deno pre post g =
  let env, _, concl = get_goal_e g in
  let cmp, f1, f2 =
    match concl.f_node with
    | Fapp({f_node = Fop(op,_)}, [f1;f2]) when is_pr f1 && is_pr f2 &&
        (EcPath.p_equal op EcCoreLib.p_eq || 
           EcPath.p_equal op EcCoreLib.p_real_le) ->
      EcPath.p_equal op EcCoreLib.p_eq, f1, f2
    | _ -> cannot_apply "equiv_deno" "" in (* FIXME error message *)
  let (ml,fl,argsl,evl) = destr_pr f1 in
  let (mr,fr,argsr,evr) = destr_pr f2 in
  let concl_e = f_equivF pre fl fr post in
  let funl = EcEnv.Fun.by_xpath fl env in
  let funr = EcEnv.Fun.by_xpath fr env in
  (* building the substitution for the pre *)
  (* we should substitute param by args and left by ml and right by mr *)
  let sargs = 
    List.fold_left2 (fun s v a -> PVM.add env (pv_loc fr v.v_name) mright a s)
      PVM.empty funr.f_sig.fs_params argsr in
  let sargs = 
    List.fold_left2 (fun s v a -> PVM.add env (pv_loc fl v.v_name) mleft a s)
      sargs funl.f_sig.fs_params argsl in
  let smem = 
    Fsubst.f_bind_mem (Fsubst.f_bind_mem Fsubst.f_subst_id mright mr) mleft ml in
  let concl_pr  = Fsubst.f_subst smem (PVM.subst env sargs pre) in
  (* building the substitution for the post *)
  let smeml = Fsubst.f_bind_mem Fsubst.f_subst_id mhr mleft in 
  let smemr = Fsubst.f_bind_mem Fsubst.f_subst_id mhr mright in
  let evl   = Fsubst.f_subst smeml evl and evr = Fsubst.f_subst smemr evr in
  let cmp   = if cmp then f_iff else f_imp in 
  let mel = EcEnv.Fun.actmem_post mleft fl funl in
  let mer = EcEnv.Fun.actmem_post mright fr funr in
  let concl_po = f_forall_mems [mel;mer] (f_imp post (cmp evl evr)) in
  prove_goal_by [concl_e;concl_pr;concl_po] rn_hl_deno g  

(* -------------------------------------------------------------------- *)
let t_ppr ty phi_l phi_r g =
  let env,_,concl = get_goal_e g in
  let ef = t_as_equivF concl in
  let fl,fr = ef.ef_fl,ef.ef_fr in

  let funl = EcEnv.Fun.by_xpath fl env in
  let funr = EcEnv.Fun.by_xpath fr env in
  let paramsl = funl.f_sig.fs_params in
  let paramsr = funr.f_sig.fs_params in
  let mk_local v =
    let v_id = EcIdent.create v.v_name in
    (v_id,v.v_type),f_local v_id v.v_type
  in
  let argsl = List.map mk_local paramsl in
  let argsr = List.map mk_local paramsr in


  let m1_id = EcIdent.create "&m1" in
  let m2_id = EcIdent.create "&m2" in
  let a_id = EcIdent.create "a" in
  let a_f = f_local a_id ty in

  (* let m1 = EcEnv.Fun.prF_memenv m1_id fl env in *)
  (* let m2 = EcEnv.Fun.prF_memenv m2_id fr env in *)
  (* memories must be abstract??!! *)
  let m1 = m1_id,None in
  let m2 = m2_id,None in

  let smem1 = Fsubst.f_bind_mem Fsubst.f_subst_id mleft mhr in
  let smem2 = Fsubst.f_bind_mem Fsubst.f_subst_id mright mhr in
  let phi1 = Fsubst.f_subst smem1 phi_l in
  let phi2 = Fsubst.f_subst smem2 phi_r in
  let pr1 = f_pr m1_id fl (List.map snd argsl) (f_eq a_f phi1) in
  let pr2 = f_pr m2_id fr (List.map snd argsr) (f_eq a_f phi2) in

  let concl_pr = f_eq pr1 pr2 in
  let smem =  
    Fsubst.f_bind_mem (Fsubst.f_bind_mem Fsubst.f_subst_id mright m2_id) mleft m1_id
  in
  let pre = Fsubst.f_subst smem ef.ef_pr in
  let concl = f_forall_mems [m1_id, EcMemory.memtype m1;m2_id,EcMemory.memtype m2] 
    (f_imp pre concl_pr) in
  let binders_l = List.map (fun ((v,t),_) -> v,GTty t ) argsl in
  let binders_r = List.map (fun ((v,t),_) -> v,GTty t ) argsr in
  let concl = f_forall_simpl binders_l (f_forall_simpl binders_r concl) in
  let concl = f_forall_simpl [a_id,GTty ty] concl in
  let concl_post = f_imps_simpl [f_eq phi_l a_f;f_eq phi_r a_f] ef.ef_po in
  let memenvl,_,memenvr,_,_ = Fun.equivS fl fr env in
  let concl_post = f_forall_mems [memenvl;memenvr] concl_post in
  let concl_post = f_forall_simpl [a_id,GTty ty] concl_post in
  prove_goal_by [concl_post;concl] rn_hl_deno g

class rn_hl_hoare_bd_hoare =
object
  inherit xrule "[hl] hoare-bd-hoare"
end

let rn_hl_hoare_bd_hoare =
  RN_xtd (new rn_hl_hoare_bd_hoare)

let t_hoare_bd_hoare g =
  let concl = get_concl g in
  if is_bdHoareS concl then
    let bhs = t_as_bdHoareS concl in
    let concl1 = f_hoareS bhs.bhs_m bhs.bhs_pr bhs.bhs_s (f_not bhs.bhs_po) in
    if f_equal bhs.bhs_bd f_r0 then
      prove_goal_by [concl1] rn_hl_hoare_bd_hoare g
    else 
      (* Rewrite this : it is a consequence rule *)
      let concl2 = 
        f_forall_mems [bhs.bhs_m] (f_imp bhs.bhs_pr (f_eq bhs.bhs_bd f_r0)) in
      prove_goal_by [concl1;concl2] rn_hl_hoare_bd_hoare g
  else if is_hoareS concl then
    let hs = t_as_hoareS concl in
    let concl1 = f_bdHoareS hs.hs_m hs.hs_pr hs.hs_s (f_not hs.hs_po) FHeq f_r0 in
    prove_goal_by [concl1] rn_hl_hoare_bd_hoare g
  else 
    cannot_apply "hoare/bd_hoare" "a hoare or bd_hoare judgment was expected" 

class rn_hl_prbounded =
object
  inherit xrule "[hl] pr-bounded"
end

let rn_hl_prbounded =
  RN_xtd (new rn_hl_prbounded)

let t_pr_bounded conseq g = 
  let env, _, concl = get_goal_e g in
  let m, pr, po, cmp, bd = 
    match concl.f_node with
    | FbdHoareF hf ->
      let m, _ = Fun.hoareF_memenv hf.bhf_f env in
      m, hf.bhf_pr, hf.bhf_po, hf.bhf_cmp, hf.bhf_bd 
    | FbdHoareS hf -> hf.bhs_m, hf.bhs_pr, hf.bhs_po, hf.bhs_cmp, hf.bhs_bd
    | _ -> tacuerror "bd_hoare excepted" in
  let cond = 
    match cmp with
    | FHle when f_equal bd f_r1 -> []
    | FHge when f_equal bd f_r0 -> []
    | _ when f_equal po f_false && f_equal bd f_r0 -> []
    (* TODO use the conseq rule instead *)
    | FHle when conseq -> [f_forall_mems [m] (f_imp pr (f_real_le f_r1 bd))]
    | FHge when conseq -> [f_forall_mems [m] (f_imp pr (f_real_le bd f_r0))]
    | _ -> cannot_apply "pr_bounded" "cannot solve the probabilistic judgement" in
  prove_goal_by cond rn_hl_prbounded g

let t_prbounded = t_pr_bounded true

(* TODO : Remove this : can be done by rewrite_pr *)
class rn_hl_prfalse =
object
  inherit xrule "[hl] pr-false"
end

let rn_hl_prfalse =
  RN_xtd (new rn_hl_prfalse)

let t_prfalse g = 
  let env,_, concl = get_goal_e g in
  let f,ev,bd =
    match concl.f_node with
      | Fapp ({f_node = Fop(op,_)}, [f;bd]) when is_pr f &&
          EcPath.p_equal op EcCoreLib.p_real_le
          || EcPath.p_equal op EcCoreLib.p_eq->
        let (_m,f,_args,ev) = destr_pr f in
        f,ev,bd
      | Fapp ({f_node = Fop(op,_)}, [bd;f]) when is_pr f &&
          EcPath.p_equal op EcCoreLib.p_eq->
        let (_m,f,_args,ev) = destr_pr f in
        f,ev,bd
      | _ ->
        cannot_apply "pr_false" "Pr[..] expression was expected"
  in
  (* the bound is zero *)
  let is_zero = f_real_le bd f_r0 in

  (* the event is false *)
  let smem_ = Fsubst.f_bind_mem Fsubst.f_subst_id mhr mhr in 
  let ev   = Fsubst.f_subst smem_ ev in
  let fun_ = EcEnv.Fun.by_xpath f env in
  let me = EcEnv.Fun.actmem_post mhr f fun_ in
  let concl_po = f_forall_mems [me] (f_imp f_false ev) in
  prove_goal_by [is_zero;concl_po] rn_hl_prfalse g

let t_bdeq g = 
  let concl = get_concl g in
  let bhs = t_as_bdHoareS concl in 
  let concl = f_bdHoareS_r {bhs with bhs_cmp=FHeq } in
  prove_goal_by [concl] rn_hl_prbounded g
    
(* -------------------------------------------------------------------- *)
class rn_hoare_true =
object
  inherit xrule "[hl] hoare-true"
end

let rn_hoare_true =
  RN_xtd (new rn_hoare_true :> xrule)

let t_hoare_true g = 
  let concl = get_concl g in
  match concl.f_node with
  | FhoareF hf when f_equal hf.hf_po f_true ->
    prove_goal_by [] rn_hoare_true g   
  | FhoareS hs when f_equal hs.hs_po f_true ->
    prove_goal_by [] rn_hoare_true g    
  | _ -> tacuerror "the conclusion should have the form hoare[_ : _ ==> true]"

let t_trivial = 
  let t1 = 
    t_lor [t_hoare_true;
           EcPhlExfalso.t_core_exfalso;   
           t_pr_bounded false;
           EcPhlSkip.t_skip] in
  t_or
    (t_lseq [t_try t_assumption; t_progress (t_id None); t_try t_assumption; 
             t1; t_trivial; t_fail])
    (t_id None)
