open EcLocation
open EcUtils
open EcMaps
open EcSymbols
open EcIdent
open EcPath
open EcCoreLib
open EcTypes
open EcFol
open EcBaseLogic
open EcEnv
open EcReduction

open EcEctoField
open EcEctoRing

type pre_judgment = {
  pj_decl : LDecl.hyps * form;
  pj_rule : (bool * int rule) option;
}

type judgment_uc = {
  juc_count : int;
  juc_map   : pre_judgment Mint.t;
}

type goals  = judgment_uc * int list
type goal   = judgment_uc * int 
type tactic = goal -> goals 

let new_goal juc decl =
  let n = juc.juc_count in
  let pj = { pj_decl = decl; pj_rule = None; } in
  let juc = 
    { juc_count = n + 1;
      juc_map   = Mint.add n pj juc.juc_map } in
  juc, n
        
let open_juc decl = 
  fst (new_goal { juc_count = 0; juc_map = Mint.empty } decl)
     
let get_pj (juc,n) =
  try Mint.find n juc.juc_map 
  with Not_found -> raise (UnknownSubgoal n)

let get_open_goal (juc,n) = 
  let g = get_pj (juc,n) in
  if g.pj_rule <> None then raise (NotAnOpenGoal (Some n));
  g
        
let upd_juc_map juc n pj = 
  { juc with juc_map = Mint.add n pj juc.juc_map }
    
let upd_done juc =
  let is_done juc = function
    | RA_node n ->
        begin match (get_pj (juc,n)).pj_rule with
        | Some(true, _) -> true
        | _ -> false 
        end
    | _ -> true in
  let rec upd juc n =
    let pj = get_pj (juc, n) in
    match pj.pj_rule with
    | None | Some(true, _) -> juc
    | Some(false,r) ->
        let juc = List.fold_left upd_arg juc r.pr_hyps in
        if List.for_all (is_done juc) r.pr_hyps then 
          upd_juc_map juc n { pj with pj_rule = Some(true,r)}
        else juc 
  and upd_arg juc = function
    | RA_node n -> upd juc n
    | _ -> juc in
  upd juc 0

let get_first_goal juc = 
  let rec aux n = 
    let pj = get_pj (juc, n) in
    match pj.pj_rule with
    | None -> juc, n 
    | Some(d, r) -> if d then raise (NotAnOpenGoal None) else auxs r.pr_hyps
  and auxs ns = 
    match ns with
    | [] -> raise (NotAnOpenGoal None) 
    | RA_node n :: ns -> (try aux n with _ -> auxs ns)
    | _ :: ns -> auxs ns in
  aux 0

let find_all_goals juc = 
  let juc = upd_done juc in
  let rec aux ns n = 
    let pj = get_pj (juc, n) in
    match pj.pj_rule with
    | None -> n :: ns
    | Some(d, r) -> if d then ns else List.fold_left auxa ns r.pr_hyps 
  and auxa ns = function
    | RA_node n -> aux ns n
    | _ -> ns in
  juc, List.rev (aux [] 0)

let close_juc juc =
  let rec close n = 
    let pj = get_pj (juc,n) in
    let hyps,concl = pj.pj_decl in
    let rule = 
      match pj.pj_rule with
      | None -> raise (StillOpenGoal n)
      | Some (_,r) ->
        { pr_name = r.pr_name;
          pr_hyps = List.map close_arg r.pr_hyps } in
    { j_decl = LDecl.tohyps hyps, concl;
      j_rule = rule }
  and close_arg = function
    | RA_form f -> RA_form f
    | RA_id id  -> RA_id id
    | RA_mp mp  -> RA_mp mp
    | RA_node n -> RA_node (close n) in
  close 0

let upd_rule d pr (juc,n as g) = 
  let pj = get_open_goal g in
  let sg = List.pmap (function RA_node n -> Some n | _ -> None) pr.pr_hyps in
  upd_juc_map juc n { pj with pj_rule = Some(d, pr) }, sg


let upd_rule_done = upd_rule true
let upd_rule      = upd_rule false

(* -------------------------------------------------------------------- *)
let rec destruct_product hyps fp =
  let module R = EcReduction in

  match EcFol.sform_of_form fp with
  | SFquant (Lforall, (x, t), f) -> Some (`Forall (x, t, f))
  | SFimp (f1, f2) -> Some (`Imp (f1, f2))
  | _ -> begin
    match R.h_red_opt R.full_red hyps fp with
    | None   -> None
    | Some f -> destruct_product hyps f
  end

(* -------------------------------------------------------------------- *)
let t_id msg (juc,n) =
  msg |> oiter (fun x -> Printf.fprintf stderr "DEBUG: %s\n%!" x);
  (juc, [n])

let t_on_goals t (juc,ln) = 
  let juc,ln = 
    List.fold_left (fun (juc,ln) n ->
      let juc,ln' = t (juc,n) in
      juc,List.rev_append ln' ln) (juc,[]) ln in
  juc,List.rev ln
        
let t_seq t1 t2 g = t_on_goals t2 (t1 g)
        
let rec t_lseq lt = 
  match lt with
  | [] -> t_id None
  | t1::lt -> t_seq t1 (t_lseq lt)

let t_subgoal lt (juc,ln) =
  let len1 = List.length lt in
  let len2 = List.length ln in
  if len1 <> len2 then raise (InvalidNumberOfTactic(len2, len1));
  let juc, ln = 
    List.fold_left2 (fun (juc,ln) t n ->
      let juc, ln' = t (juc, n) in
      juc, List.rev_append ln' ln) (juc,[]) lt ln in
  juc, List.rev ln

let t_on_nth t n (juc,ln) = 
  let r,n,l = try List.split_n n ln with _ -> assert false in
  let juc,ln = t (juc,n) in
  juc, List.rev_append r (List.append ln l)

let t_on_firsts t i (juc, ln) =
  let (ln1, ln2) = List.take_n i ln in
  snd_map (List.append^~ ln2) (t_on_goals t (juc, ln1))

let t_on_lasts t i (juc, ln) =
  let (ln1, ln2) = List.take_n (max 0 (List.length ln - i)) ln in
  snd_map (List.append ln1) (t_on_goals t (juc, ln2))

let t_on_first t g = t_on_firsts t 1 g
let t_on_last  t g = t_on_lasts  t 1 g

let t_seq_subgoal t lt g = t_subgoal lt (t g)

let t_try_base t g =
  let rec is_user_error = function
    | TacError (true, _) -> true
    | LocError (_, e)    -> is_user_error e
    | _ -> false
  in
  try `Success (t g)
  with e when is_user_error e -> `Failure e

let t_fail _g = tacuerror "FAIL TACTIC"

let t_try t g =
  match t_try_base t g with
  | `Failure _ -> t_id None g
  | `Success g -> g

let t_or t1 t2 g = 
  match t_try_base t1 g with
  | `Failure _ -> t2 g
  | `Success g -> g

let rec t_lor lt g = 
  match lt with
  | [] -> t_fail g 
  | t1::lt -> t_or t1 (t_lor lt) g

let t_do b omax t g =
  let max = max (odfl max_int omax) 0 in

  let rec doit i g =
    let r = if i < max then Some (t_try_base t g) else None in

    match r with
    | None -> t_id None g

    | Some (`Failure e) ->
        let fail =
          match b, omax with
          | `Maybe, _      -> false
          | `All  , None   -> i < 1
          | `All  , Some m -> i < m
        in
          if fail then raise e else t_id None g

    | Some (`Success (juc, ln)) -> 
        t_subgoal (List.map (fun _ -> doit (i+1)) ln) (juc, ln)
  in
    doit 0 g

let t_repeat t = t_do `Maybe None t

let t_close t g =
  match t g with
  | (juc, []    ) -> (juc, [])
  | (_  , i :: _) -> raise (StillOpenGoal i)

let t_rotate mode sz (juc, ns) =
  let mrev = match mode with `Left -> identity | `Right -> List.rev in
  let sz   = if ns = [] then 0 else (max 0 sz) mod List.length ns in

  let (hd, tl) = List.take_n sz (mrev ns) in (juc, mrev (tl @ hd))

(* -------------------------------------------------------------------- *)
let get_node  g = (get_pj g).pj_decl
let get_goal  g = (get_open_goal g).pj_decl

let get_goal_e g = 
  let hyps, concl = get_goal g in
  LDecl.toenv hyps, hyps, concl

let get_hyps  g = fst (get_goal g)
let get_concl g = snd (get_goal g)

(* -------------------------------------------------------------------- *)
let tacerror = EcBaseLogic.tacerror 

let tacuerror = EcBaseLogic.tacuerror

let cannot_apply s1 s2 = 
  tacuerror "Can not apply %s tactic:@\n %s" s1 s2

(* -------------------------------------------------------------------- *)
let t_subgoal lt gs =
  try
    t_subgoal lt gs
  with
  | InvalidNumberOfTactic (i1, i2) ->
      tacerror (InvalNumOfTactic (i1, i2))

let t_admit g =
  let rule = { pr_name = RN_admit; pr_hyps = [] } in
  upd_rule_done rule g

let check_hyps hyps1 hyps2 =
  assert (hyps1 == hyps2) (* FIXME error message *)

(* WARNING this do not generate the subgoal included in n.
   It could be greater to ensure we have no circular dependency *)
(* Use the proof of n1 to prove n *)
let use_node juc n n1 =
  let hyps,concl = get_node (juc,n) in
  let hyps',concl' = get_goal (juc,n1) in
  check_hyps hyps hyps';
  check_conv hyps concl concl';
  let rule = { pr_name = RN_conv; pr_hyps = [RA_node n] } in
  fst (upd_rule rule (juc,n1))

let t_use n gs (juc,n1) =
  use_node juc n n1, gs

let t_change f (juc,n1) =
  let hyps = get_hyps (juc,n1) in
  check_type (LDecl.toenv hyps) f.f_ty tbool;
  let (juc,n) = new_goal juc (hyps,f) in
  t_use n [n] (juc,n1)

let t_red g =
  let hyps, concl = get_goal g in
  let f = EcReduction.h_red EcReduction.full_red hyps concl in
  t_change f g

let t_simplify ri (juc,n1 as g) =
  let hyps, concl = get_goal g in
  let f = EcReduction.simplify ri hyps concl in
  let (juc,n) = new_goal juc (hyps,f) in
  let rule = { pr_name = RN_conv; pr_hyps = [RA_node n] } in
  upd_rule rule (juc,n1)

let t_simplify_nodelta g = 
  let ri = 
    { full_red with delta_h = Some Mid.empty; 
      delta_p = Some EcPath.Mp.empty } in 
  t_simplify ri g
  
let mkn_hyp juc hyps id =
  let f = LDecl.lookup_hyp_by_id id hyps in
  let juc,n = new_goal juc (hyps,f) in
  let rule = { pr_name = RN_hyp id; pr_hyps = [] } in
  let juc, _ = upd_rule_done rule (juc,n) in
  juc, n

let t_hyp id (juc,n as g) =
  let hyps = get_hyps g in
  let juc,nh = mkn_hyp juc hyps id in
  use_node juc nh n, []

let mkn_glob juc hyps p tys =
  let f = Ax.instanciate p tys (LDecl.toenv hyps) in
  let juc, n = new_goal juc (hyps,f) in
  let rule = { pr_name = RN_glob(p,tys); pr_hyps = [] } in
  let juc, _ = upd_rule_done rule (juc, n) in
  juc, n

let t_glob p tys (juc,n as g) =
  let hyps = get_hyps g in
  let juc, nh = mkn_glob juc hyps p tys in
  use_node juc nh n, []

let t_smt ~strict ~usehyps pi g =
  let error = tacuerror ~catchable:(not strict) in

  let _,concl as goal = get_goal g in
  match concl.f_node with
    | FequivF   _  | FequivS   _
    | FhoareF   _  | FhoareS   _
    | FbdHoareF _  | FbdHoareS _ -> 
      tacuerror "Cannot process program judgement, use skip tactic first"

    | _ ->
        try
          if EcEnv.check_goal ~usehyps pi goal then
            let rule = { pr_name = RN_prover (); pr_hyps = [] } in
            upd_rule_done rule g
          else error "cannot prove goal"
        with EcWhy3.CanNotTranslate _ ->
          error "cannot prove goal"

let t_clear ids (juc,n as g) =
  let pp_id fmt id = Format.fprintf fmt "%s" (EcIdent.name id) in
  let hyps,concl = get_goal g in
  if not (Mid.set_disjoint ids concl.f_fv) then begin
    let elts = Sid.elements (Mid.set_inter ids concl.f_fv) in
    tacuerror 
      "Cannot clear %a, %s used in the conclusion"
      (EcPrinting.pp_list ",@ " pp_id) elts
      (if List.length elts = 1 then "it is" else "they are")
  end;
  let hyps = 
    try LDecl.clear ids hyps 
    with LDecl.Ldecl_error (LDecl.CanNotClear(id1,id2)) ->
      tacuerror "Cannot clear %a it is used in %a"
        pp_id id1 pp_id id2 in
  let juc,n1 = new_goal juc (hyps,concl) in
  let rule = { pr_name = RN_clear ids; pr_hyps = [RA_node n1] } in
  upd_rule rule (juc,n)

let gen_check_restr env pp_a a use restr =
  let restr = NormMp.norm_restr env restr in 
  let ppe = EcPrinting.PPEnv.ofenv env in
  let pp_mp = EcPrinting.pp_topmod ppe in
  let check_xp xp _ = 
    (* We check that the variable is not a variable in restr *)
    if NormMp.use_mem_xp xp restr then
      tacuerror "%a should not use the variable %a."
       (pp_a ppe) a (EcPrinting.pp_pv ppe) (pv_glob xp);
    (* We check that the variable is in the restriction of the abstract module
       in restr *)
    let check id2 = 
      let mp2 = EcPath.mident id2 in
      let r2  = NormMp.get_restr env mp2 in
      if not (NormMp.use_mem_xp xp r2) then
        tacuerror "%a use the variable %a, but should not use the module %a (which can use %a)" (pp_a ppe) a (EcPrinting.pp_pv ppe) (pv_glob xp)
          pp_mp mp2 (EcPrinting.pp_pv ppe) (pv_glob xp) in
    EcIdent.Sid.iter check restr.NormMp.us_gl in
  EcPath.Mx.iter check_xp (use.NormMp.us_pv);
  let check_gl id = 
    let mp1 = EcPath.mident id in
    if NormMp.use_mem_gl mp1 restr then
      tacuerror "%a should not use the module %a."
        (pp_a ppe) a pp_mp mp1
    else 
      let r1 = NormMp.get_restr env mp1 in
      let check id2 = 
        let mp2 = EcPath.mident id2 in
        if not (NormMp.use_mem_gl mp2 r1) then
          let r2 = NormMp.get_restr env mp2 in
          if not (NormMp.use_mem_gl mp1 r2) then
            tacuerror 
              "%a, using %a, should not use %a; add restriction %a to %a or %a to %a"
            (pp_a ppe) a pp_mp mp1 pp_mp mp2 
            pp_mp mp1 pp_mp mp2 pp_mp mp2 pp_mp mp1 in
      EcIdent.Sid.iter check restr.NormMp.us_gl in
  EcIdent.Sid.iter check_gl use.NormMp.us_gl


let check_restr env mp restr = 
  let use = NormMp.mod_use env mp in
  let pp_mod ppe fmt mp = 
    Format.fprintf fmt "The module %a" (EcPrinting.pp_topmod ppe) mp in
  gen_check_restr env pp_mod mp use restr
       
let check_modtype_restr env mp mt i restr =
  begin
    try EcTyping.check_sig_mt_cnv env mt i
    with EcTyping.TymodCnvFailure e ->
      let ppe = EcPrinting.PPEnv.ofenv env in
      tacuerror "%a : %a"
        (EcPrinting.pp_topmod ppe) mp
        (fun fmt e -> EcTyping.pp_cnv_failure fmt env e) e
  end;
  check_restr env mp restr

type app_arg =
  | AAform of form
  | AAmem  of EcIdent.t
  | AAmp   of EcPath.mpath * EcModules.module_sig 
  | AAnode

type 'a app_arg_cb = LDecl.hyps -> gty option -> 'a -> app_arg

let check_arg do_arg hyps s x gty a =
  let gty = Fsubst.gty_subst s gty in
  let a = do_arg hyps (Some gty) a in
  match gty, a with
  | GTty ty  , AAform f ->
      check_type (LDecl.toenv hyps) ty f.f_ty; (* FIXME error message *)
      Fsubst.f_bind_local s x f, RA_form f
  | GTmem _   , AAmem m ->
      Fsubst.f_bind_mem s x m, RA_id m
  | GTmodty (emt, restr), AAmp (mp, mt)  ->
    let env = (LDecl.toenv hyps) in
    check_modtype_restr env mp mt emt restr;
    EcPV.check_module_in env mp emt;
    Fsubst.f_bind_mod s x mp, RA_mp mp
  | _ -> assert false (* FIXME error message *)

let mkn_apply do_arg (juc,n) args =
  if args = [] then (juc,n), []
  else
    let hyps,concl = get_node (juc,n) in
    let check_arg = check_arg do_arg hyps in
    let rec check_apply juc s ras f args =
      match args with
      | [] -> juc, List.rev ras, Fsubst.f_subst s f
      | a :: args' ->
        if is_forall f then 
          let (x,gty,f') = destr_forall1 f in
          let s, ra = check_arg s x gty a in
          check_apply juc s (ra::ras) f' args' 
        else if is_imp f then 
          let (f1,f2) = destr_imp f in
          let a = do_arg hyps None a in
          assert (a = AAnode); (* FIXME error message *)
          let juc, n = new_goal juc (hyps, Fsubst.f_subst s f1) in
          check_apply juc s (RA_node n :: ras) f2 args' 
        else 
          let f = Fsubst.f_subst s f in
          match h_red_opt full_red hyps f with
          | None -> tacerror TooManyArguments
          | Some f -> check_apply juc Fsubst.f_subst_id ras f args in
    let juc, ras, concl = check_apply juc Fsubst.f_subst_id [] concl args in
    let (juc,n1) = new_goal juc (hyps,concl) in
    let rule = { pr_name = RN_apply; pr_hyps = RA_node n :: ras} in
    let juc, _ = upd_rule rule (juc,n1) in
    let ns = List.pmap (function RA_node n -> Some n | _ -> None) ras in
    (juc,n1), ns

let gen_t_apply do_arg fn args (juc,n) =
  let (juc,an), ns = mkn_apply do_arg (juc,fn) args in
  (use_node juc an n, ns)

let gen_t_apply_form do_arg f args (juc, n as g) =
  let hyps = get_hyps g in
  let juc, fn = new_goal juc (hyps, f) in
  let juc,ns = gen_t_apply do_arg fn args (juc,n) in
  juc, fn::ns

let t_apply_form = gen_t_apply_form (fun _ _ a -> a)

let gen_t_apply_glob do_arg p tys args (juc,n as g) =
  let hyps = get_hyps g in
  let juc,fn = mkn_glob juc hyps p tys in
  gen_t_apply do_arg fn args (juc,n)

let t_apply_glob = gen_t_apply_glob (fun _ _ a -> a)

let gen_t_apply_hyp do_arg id args (juc ,n as g) =
  let hyps = get_hyps g in
  let juc,fn = mkn_hyp juc hyps id in
  gen_t_apply do_arg fn args (juc, n)

let t_apply_hyp = gen_t_apply_hyp (fun _ _ a -> a)

let check_logic env p =
  try  ignore (EcEnv.Ax.by_path p env)
  with EcEnv.LookupFailure _ -> assert false

let t_apply_logic p tyargs args g =
  check_logic (LDecl.toenv (get_hyps g)) p;
  t_apply_glob p tyargs args g
  
let pattern_form name hyps f1 f =
  let x = EcIdent.create (odfl "x" name) in
  let fx = EcFol.f_local x f1.f_ty in
  let body =
    Hf.memo_rec 107
      (fun aux f ->
        if EcReduction.is_alpha_eq hyps f f1 then fx
        else f_map (fun ty -> ty) aux f)
      f in
  x, body

type dofpattern = LDecl.hyps -> form -> form -> (EcIdent.t * form)

let t_rewrite_gen fpat side f g = 
  let side = match side with `LtoR -> true | `RtoL -> false in
  let hyps,concl = get_goal g in
  let env = LDecl.toenv hyps in
  let rec find_rewrite f =
    if is_eq f then destr_eq f, `Eq
    else if is_iff f then destr_iff f, `Eqv
    else
      match h_red_opt full_red hyps f with
      | Some f -> find_rewrite f
      | None   -> begin
        if side && (EcReduction.equal_type env f.f_ty EcTypes.tbool)
        then ((f, f_true), `Bool)
        else
          let ppe = EcPrinting.PPEnv.ofenv (LDecl.toenv hyps) in
            tacuerror "Do not known how to rewrite %a" (EcPrinting.pp_form ppe) f
      end in
  let (f1,f2),mode = find_rewrite f in
  let p,tys, fs =
    match mode with
    | `Eq   -> (if side then p_rewrite_l else p_rewrite_r), [f1.f_ty], [AAform f1; AAform f2]
    | `Eqv  -> (if side then p_rewrite_iff_l else p_rewrite_iff_r), [], [AAform f1; AAform f2]
    | `Bool -> p_rewrite_bool, [], [AAform f1] in
  let pred =
    let f = if side then f1 else f2 in
    let x, body = fpat hyps f concl in
    f_lambda [x,GTty f.f_ty] body in
  t_on_last
    t_red 
    (t_apply_logic p tys (fs @ [AAform pred;AAnode;AAnode]) g)

let t_rewrite = t_rewrite_gen (pattern_form None)

let t_rewrite_node ?(fpat = pattern_form None) ((juc,an), gs) side n =
  let (_,f) = get_node (juc, an) in
  t_seq_subgoal (t_rewrite_gen fpat side f) [t_use an gs;t_id None] (juc,n)

let t_rewrite_hyp ?fpat side id args (juc,n as g) =
  let g = mkn_hyp juc (get_hyps g) id in
  t_rewrite_node ?fpat (mkn_apply (fun _ _ a -> a) g args) side n

let t_rewrite_glob ?fpat side p tys args (juc,n as g) =
  let g = mkn_glob juc (get_hyps g) p tys in
  t_rewrite_node ?fpat (mkn_apply (fun _ _ a -> a) g args) side n

let t_rewrite_form ?fpat side fp args (juc, n as g) =
  let (juc, fn) = new_goal juc (get_hyps g, fp) in
  let g = mkn_apply (fun _ _ a -> a) (juc, fn) args in
  let g = t_rewrite_node ?fpat g side n
  in
    snd_map (fun ns -> fn :: ns) g

let t_cut f g =
  let concl = get_concl g in
  t_apply_logic p_cut_lemma [] [AAform f;AAform concl;AAnode;AAnode] g

let set_loc loc f x =
  try f x
  with e -> EcLocation.locate_error loc e

let t_intros ids (juc,n as g) =
  let hyps, concl = get_goal g in
  let add_local s id x gty =
    let id   = id.pl_desc in
    let name = EcIdent.name id in
    let gty  = Fsubst.gty_subst s gty in
    match gty with
    | GTty ty ->
        if name <> "_" && not (EcIo.is_sym_ident name) then
          tacerror (InvalidName name);
        LD_var(ty,None), Fsubst.f_bind_local s x (f_local id ty)

    | GTmem me ->
        if name <> "_" && not (EcIo.is_mem_ident name) then
          tacerror (InvalidName name);
        LD_mem me, Fsubst.f_bind_mem s x id

    | GTmodty (i,r) ->
        if name <> "_" && not (EcIo.is_mod_ident name) then
          tacerror (InvalidName name);
        LD_modty (i,r), Fsubst.f_bind_mod s x (EcPath.mident id)
  in

  let add_ld id ld hyps =
    set_loc id.pl_loc (LDecl.add_local id.pl_desc ld) hyps in

  let rec check_intros hyps ids s concl =
    match ids with
    | [] -> hyps, Fsubst.f_subst s concl
    | id::ids' ->
      if is_forall concl then
        let (x,gty,concl) = destr_forall1 concl in
        let ld, s = add_local s id x gty in
        let hyps = add_ld id ld hyps in
        check_intros hyps ids' s concl
      else if is_imp concl then
        let f1, f2 = destr_imp concl in
        let hyps = add_ld id (LD_hyp (Fsubst.f_subst s f1)) hyps in
        check_intros hyps ids' s f2
      else if is_let concl then
        let x,ty,e1,concl = destr_let1 concl in
        let s = Fsubst.f_bind_local s x (f_local id.pl_desc ty) in
        let hyps = add_ld id (LD_var (s.fs_ty ty, Some (Fsubst.f_subst s e1))) hyps in
        check_intros hyps ids' s concl
      else if s == Fsubst.f_subst_id then
        match h_red_opt full_red hyps concl with
        | None -> 
          let ppe = EcPrinting.PPEnv.ofenv (LDecl.toenv hyps) in
          tacuerror "Do not known what to introduce in %a"
            (EcPrinting.pp_form ppe) concl
        | Some concl -> check_intros hyps ids s concl
      else check_intros hyps ids Fsubst.f_subst_id (Fsubst.f_subst s concl) in
  let hyps, concl = check_intros hyps ids Fsubst.f_subst_id concl in
  let (juc,n1) = new_goal juc (hyps,concl) in
  let ids = List.map unloc ids in
  let rule = { pr_name = RN_intros ids; pr_hyps = [RA_node n1]} in
  upd_rule rule (juc,n)

(* internal use *)
let t_intros_i ids g =
  t_intros 
    (List.map (fun id -> {pl_desc = id; pl_loc = EcLocation._dummy}) ids)
    g

let t_intros_1 ids g =
  match t_intros_i ids g with
  | (juc, [n]) -> (juc, n)
  | _ -> assert false

let createVarForBinding t =
  let v = EcIdent.create "_" in ((v, GTty t),EcFol.f_local v t)

let createVarForLet t =
  let v = EcIdent.create "_" in ((v, t), EcFol.f_local v t)

let t_reflex ?(reduce = false) g =
  let hyps = get_hyps g in

  let rec doit goal =
    let notaneq () = tacuerror "reflexivity: not an equality" in
      match EcFol.sform_of_form goal with
      | SFeq (f, _) ->
          t_apply_logic p_eq_refl [f.f_ty] [AAform f] g
      | _ when reduce -> begin
        match EcReduction.h_red_opt EcReduction.full_red hyps goal with
        | None      -> notaneq ()
        | Some goal -> doit goal
      end
      | _ -> notaneq ()
  in
    doit (get_concl g)

let t_transitivity f g =
  let concl = snd (get_goal g) in
  let (f1, f2) = destr_eq concl in
    t_apply_logic
      p_eq_trans [f.f_ty]
      (  (List.map (fun f -> AAform f) [f1; f; f2])
       @ (List.create 2 AAnode))
      g

(* Use to create two set of vars of a list of types*)
let parseType create types =
  let parse ty =
    let (bX, fX) = create ty in
    let (bY, fY) = create ty in
    ((bX, bY), (fX, fY))
  in
  List.split (List.map parse types)

(* Generate a lemma that permits to elim a tuple *)
let gen_eq_tuple_elim_lemma types =
  let (bC, fC) = createVarForBinding EcTypes.tbool in
  let (vars, fvars) = parseType createVarForBinding types in
  let (varsx, varsy) = List.split vars in
  let (fvarsx, fvarsy) = List.split fvars in
  let bindings = varsx@varsy@[bC] in
  let hyp1 = f_eq (f_tuple fvarsx) (f_tuple fvarsy) in
  let hyp2 = f_imps (List.map (fun (x,y) -> f_eq x y) fvars) fC in
  f_forall bindings (f_imps [hyp1; hyp2] fC)

(* Generate a proof of eq_tuple_elim *)
let gen_eq_tuple_elim_proof types =
  let pred rvars fc =
    let (bT, fT) = createVarForBinding (ttuple types) in
    let projs = List.map createVarForLet types in
    let (intro, fprojs) = List.split projs in
    let introTu = LTuple intro in
    let eqs = List.map (fun (x, y) -> f_eq x y) (List.combine fprojs rvars) in
    let body = f_imps eqs fc in
    f_app (f_lambda [bT] (f_let introTu fT body)) [f_tuple rvars] (EcTypes.tbool)
  in
  
  let (locVars, locVarsF) = parseType createVarForLet types in
  let (locC, locCF) = createVarForLet EcTypes.tbool in
  let introVars =
    let (a, b) = List.split locVars in
    fst (List.split (a@b@[locC]))
  in
  let (_, rvars) = List.split locVarsF in
  let h1 = EcIdent.create "_" in
  let h2 = EcIdent.create "_" in
  let intro = t_intros_i (introVars@[h1;h2]) in
  t_lseq [
    intro;
    t_seq_subgoal
      (t_apply_form (pred rvars locCF) (List.map (fun _ -> AAnode) types))
      ((
        t_lseq [t_rewrite_hyp `RtoL h1 [];
        t_apply_hyp h2 [];
        t_apply_logic p_true_intro [] []]
      )::(List.map (fun _ -> t_reflex ~reduce:false) types))
  ]
  
(* Generate a lemma that permits to split tuple *)
let gen_split_tuple_lemma types =
  let (vars, fvars) = parseType createVarForBinding types in
  let (varsx, varsy) = List.split vars in
  let (fvarsx, fvarsy) = List.split fvars in
  let bindings = varsx@varsy in
  let hyps = List.map (fun (x,y) -> f_eq x y) fvars in
  let body = f_eq (f_tuple fvarsx) (f_tuple fvarsy) in
  f_forall bindings (f_imps hyps body)

(* Generate the proof for gen_split_tuple_proof *)
let gen_split_tuple_proof types =
  let introVars = List.map (fun _ -> EcIdent.create "_") (types@types) in
  let introHyps = List.map (fun _ -> EcIdent.create "_") types in
  let rews = List.map (fun h -> t_rewrite_hyp `RtoL h []) introHyps in
  t_seq (t_lseq ((t_intros_i (introVars@introHyps))::rews)) t_reflex

let t_elim f (juc,n) =
  let hyps,concl = get_goal (juc,n) in
  let rec aux f =
    match f.f_node with
    | Fop(p,_) when EcPath.p_equal p p_false ->
      t_apply_logic p_false_elim [] [AAform concl; AAnode] (juc,n)

    | Fapp({f_node = Fop(p,_)}, [a1;a2] ) ->
      begin
        match op_kind p with
        | OK_and b ->
          t_apply_logic (if b then p_anda_elim else p_and_elim) []
                [AAform a1;AAform a2;AAform concl;AAnode;AAnode] (juc,n)
        | OK_or b  ->
          t_apply_logic (if b then p_ora_elim else p_or_elim) []
                [AAform a1;AAform a2;AAform concl;AAnode;AAnode;AAnode] (juc,n)
        | OK_iff   -> 
          t_apply_logic p_iff_elim []
                [AAform a1;AAform a2;AAform concl;AAnode;AAnode] (juc,n)
        | OK_eq when is_tuple a1 && is_tuple a2 ->
          let fs1 = destr_tuple a1 in
          let fs2 = destr_tuple a2 in
          let types = List.map (fun v -> v.f_ty) fs1 in
          let args = List.map (fun f -> AAform f) (fs1 @ fs2 @ [concl]) in
          let lemma = gen_eq_tuple_elim_lemma types in
          let proof = gen_eq_tuple_elim_proof types in
          let gs = t_apply_form lemma (args@[AAnode; AAnode]) (juc,n) in
          t_on_first proof gs
        | _        -> aux_red f
      end
    | Fif(a1,a2,a3) ->
      t_apply_logic p_if_elim [] [AAform a1;AAform a2;AAform a3;
                                     AAform concl;AAnode;AAnode;AAnode] (juc,n)
    | Fquant(Lexists,bd,f') ->
      let juc,n1 = new_goal juc (hyps, f) in
      let juc,n2 = new_goal juc (hyps,f_forall bd (f_imp f' concl)) in
      let rule = { pr_name = RN_exists_elim; pr_hyps = [RA_node n1; RA_node n2] } in
      upd_rule rule (juc, n)
    | _ -> aux_red f

  and aux_red f =
    match h_red_opt full_red hyps f with
    | Some f -> aux f
    | _ -> 
      let ppe = EcPrinting.PPEnv.ofenv (LDecl.toenv hyps) in
      tacuerror 
        "Do not known what to eliminate in %a" (EcPrinting.pp_form ppe) f in
  aux f

let t_elim_hyp h g =
  let f = LDecl.lookup_hyp_by_id h (get_hyps g) in
  t_on_first (t_hyp h) (t_elim f g)

(*Field and Ring Tactic****************************************************************************************)
let prove_goal_by sub_gs rule (juc,n as g) : goals =
  let hyps,_ = get_goal g in
  let add_sgoal (juc,ns) sg = 
    let juc,n = new_goal juc (hyps,sg) in juc, RA_node n::ns
  in
  let juc,ns = List.fold_left add_sgoal (juc,[]) sub_gs in
  let rule = { pr_name = rule ; pr_hyps = List.rev ns} in
  upd_rule rule (juc,n)

let ringax plus times exp minus z o eq =
  let ty = z.f_ty in
  let mkf f = mk_form f ty in
  let cid t = let i = EcIdent.create t in (mkf (Flocal i),i) in 
  let a1 = (* forall (a b c : ty), (a (+) b) (+) c = a (+) (b (+) c) *)
    let (fa, a) = cid "a" in
    let (fb, b) = cid "b" in
    let (fc, c) = cid "c" in
    let tab = mkf (Fapp (plus, fa :: fb :: [])) in
    let tbc = mkf (Fapp (plus, fb :: fc :: [])) in
    let t1 = mkf (Fapp (plus, fa :: tbc :: [])) in
    let t2 = mkf (Fapp (plus, tab :: fc :: [])) in
    let t = mk_form (Fapp (eq, t1 :: t2 :: [])) tbool in
    f_forall [(a,GTty ty);(b,GTty ty);(c,GTty ty)] t in
  let a2 = (* forall (a b : ty), a (+) b = b (+) a *)
    let (fa, a) = cid "a" in
    let (fb, b) = cid "b" in
    let t1 = Fapp (plus, fa :: fb :: []) in
    let t2 = Fapp (plus, fb :: fa :: []) in
    let t = mk_form (Fapp (eq, (mkf t1) :: (mkf t2) :: [])) tbool in
    f_forall ([(a, GTty ty);(b,GTty ty)]) t in
  let a3 = (* forall (a : ty), a (+) O = a *)
    let (fa, a) = cid "a" in
    let t1 = Fapp (plus, fa :: z :: []) in
    let t = mk_form (Fapp (eq, (mkf t1) :: fa :: [])) tbool in
    f_forall [a, GTty ty] t in
  let a4 = (* forall (a : ty), a (-) a = O *)
    let (fa, a) = cid "a" in
    let t1 = mkf (Fapp (minus, fa :: fa :: [])) in
    let t = mk_form (Fapp (eq, t1 :: z :: [])) tbool in
    f_forall [a, GTty ty] t in
  let m1 = (* forall (a b c : ty), (a*b)*c =a*(b*c) *)
    let (fa, a) = cid "a" in
    let (fb, b) = cid "b" in
    let (fc, c) = cid "c" in
    let tab = mkf (Fapp (times, fa :: fb :: [])) in
    let tbc = mkf (Fapp (times, fb :: fc :: [])) in
    let t1 = mkf (Fapp (times, fa :: tbc :: [])) in
    let t2 = mkf (Fapp (times, tab :: fc :: [])) in
    let t = mk_form (Fapp (eq, t1 :: t2 :: [])) tbool in
    f_forall [(a,GTty ty);(b,GTty ty);(c,GTty ty)] t in
  let d1 = (*forall (a b c : ty), a * (b (+) c) = a * b (+) a * c *)
    let (fa, a) = cid "a" in
    let (fb, b) = cid "b" in
    let (fc, c) = cid "c" in
    let fbc = mkf (Fapp (plus, fb :: fc :: [])) in
    let t1 = mkf (Fapp (times , fa :: fbc :: [])) in
    let fab = mkf (Fapp (times , fa :: fb :: [])) in
    let fac = mkf (Fapp (times , fa :: fc :: [])) in
    let t2 = mkf (Fapp (plus, fab :: fac :: [])) in
    let t = mk_form (Fapp (eq, t1 :: t2 :: [])) tbool in
    f_forall [(a,GTty ty);(b,GTty ty);(c,GTty ty)] t in
  let m2 =(* forall (a b : ty), a * b = b * a *)
    let (fa, a) = cid "a" in
    let (fb, b) = cid "b" in
    let t1 = Fapp (times, fa :: fb :: []) in
    let t2 = Fapp (times, fb :: fa :: []) in
    let t = mk_form (Fapp (eq, (mkf t1) :: (mkf t2) :: [])) tbool in
    f_forall ([(a, GTty ty);(b,GTty ty)]) t in
  let e2 = (* forall p <> O => p ^ 0 = 1 *)
    let (fa,a) = cid "a" in
    let pc = f_not (mk_form (Fapp (eq, fa :: z :: []))  tbool) in
    let t1 = mkf (Fapp (exp, fa :: (f_int 0) :: [])) in
    let t = mk_form (Fapp (eq,t1 :: o :: [])) tbool in
    f_forall [(a,GTty ty)] (f_imp pc t) in
  let e3 = (* forall p \in ty, forall i \in Int, p <> O /\ i > 0 => p ^ i = p * p ^ i *)
    let (fp,p) = cid "p" in
    let (fi, i) = let j = EcIdent.create "i" in (mk_form (Flocal j) tint, j) in
    let precd1 = f_not(mk_form (Fapp (eq, fp :: z :: [])) tbool) in
    let precd2 = f_int_lt (f_int 0) fi in
    let fim1 = f_int_sub fi (f_int 1) in
    let t = mkf (Fapp (exp, fp :: fi :: [])) in
    let t1 = mkf (Fapp (exp, fp :: fim1 :: [])) in
    let t' = mkf (Fapp (times, fp :: t1 :: [])) in
    let ee = mk_form (Fapp (eq, t' :: t :: [])) tbool in
    f_forall [(p,GTty ty);(i,GTty tint)] (f_imp precd1 (f_imp precd2 ee)) in
    e2 :: e3 :: a1 :: a2 :: a3 :: a4 :: m1 :: m2 :: d1 :: []

let fieldax plus times exp minus inv div z o eq =
  let ring = ringax plus times exp minus z o eq in
  let ty = z.f_ty in
  let mkf f = mk_form f ty in
  let cid t = let i = EcIdent.create t in (mkf (Flocal i),i) in 
  let m3 = (* forall (a : ty), a * 1 = 1 *)
    let (fa, a) = cid "a" in
    let t1 = Fapp (times, fa :: o :: []) in
    let t = mk_form (Fapp (eq, (mkf t1) :: fa :: [])) tbool in
    f_forall [a, GTty ty] t in
  let m4 = (* forall (a : ty), a <> O => a * inv a = 1 *)
    let (fa, a) = cid "a" in
    let precond =  f_not (mkf (Fapp (eq, fa :: z :: []))) in
    let infa = mkf (Fapp (inv, fa :: [])) in
    let t1 = mkf (Fapp (times, fa :: infa :: [])) in
    let t = mk_form (Fapp (eq, t1 :: o :: [])) tbool in
    f_forall [a, GTty ty] (f_imp precond t) in
  let dff = f_not (mk_form (Fapp(eq, o :: z :: [])) tbool) in
  let divinv = (* forall (x : ty), inv(x) = 1 / x *)
    let (fa, a) = cid "a" in
    let precond =  f_not (mkf (Fapp (eq, fa :: z :: []))) in
    let x1 = mkf (Fapp (div, o :: fa :: [])) in
    let ix = mkf (Fapp (inv, fa :: [])) in
    let t = mk_form (Fapp (eq,x1 :: ix :: [])) tbool in
    f_forall [(a, GTty ty)] (f_imp precond t) in
  divinv :: dff :: m3 :: m4 :: ring

let t_field (plus,times,inv,exp,minus,div,z,o,eq,eqs) (t1,t2) : tactic =
  (fun g ->
	let (pzs,(d1,d2),(n1,n2)) = appfield (t1, t2) plus minus times inv exp div z o eqs in
  let rg = (fun (t1,t2) -> ring_eq t1 t2 plus minus times exp z o eqs) in
  let res = rg (mk_form (Fapp (times, n1 :: d2 :: [])) z.f_ty,mk_form (Fapp (times, n2 :: d1 :: [])) z.f_ty) in
	let pzs' = List.fold_left (fun is i -> (f_not (mk_form (Fapp (eq, [i;z])) tbool)) :: is) [] pzs in
  let ax = fieldax plus times exp minus inv div z o eq in
  if (f_equal res z) then
    prove_goal_by (pzs' @ ax) RN_field g 
  else
    let t = mk_form (Fapp (eq, res :: z :: [])) tbool in 
    prove_goal_by ( t :: pzs' @ ax) RN_field g)

let t_field_simp (plus,times,inv,exp,minus,div,z,o,eq,eqs) (t1,t2) : tactic =
  (fun g ->
	let (pzs,rn,rd) = appfield_simp t1 plus minus times inv exp div z o eqs in
	let (pzs',rn',rd') = appfield_simp t2 plus minus times inv exp div z o eqs in
  let r    = mk_form (Fapp (div, rn :: rd :: [])) z.f_ty in
  let r'   = mk_form (Fapp (div, rn' :: rd' :: [])) z.f_ty in
  let t    = mk_form (Fapp (eq, r :: r' :: [])) tbool in
	let ps'  = List.fold_left (fun is i -> (f_not (mk_form (Fapp (eq, [i;z])) tbool)) :: is) [] pzs in
	let psa' = List.fold_left (fun is i -> (f_not (mk_form (Fapp (eq, [i;z])) tbool)) :: is) [] pzs' in
  let ax   = fieldax plus times exp minus inv div z o eq in
  prove_goal_by (t :: (ps' @ psa') @ ax) RN_field g) 

let t_field_simp_s (plus,times,inv,exp,minus,div,z,o) t1 : (form list * form * form) =
  appfield_simp t1 plus minus times inv exp div z o []

let t_ring_simp_s (plus,times,exp,minus,z,o) t1 : form =
  ring_simp t1 plus minus times exp z o []

  
let t_ring_simp  (plus,times,exp,minus,z,o,eq,eqs) (t1,t2) : tactic =
  (fun g ->
  let pbs1 = ring_simp t1 plus minus times exp z o eqs in
  let pbs2 = ring_simp t2 plus minus times exp z o eqs in
  let ax = ringax plus times exp minus z o eq in
	prove_goal_by ((mk_form (Fapp (eq,pbs1::pbs2::[])) tbool) :: ax) RN_ring g)

let t_ring  (plus,times,exp,minus,z,o,eq,eqs) (t1,t2) : tactic =
  (fun g ->
  let res = ring_eq t1 t2 plus minus times exp z o eqs in
  let ax = ringax plus times exp minus z o eq in
  if (f_equal res z) then
    prove_goal_by ax RN_ring g
  else  
    prove_goal_by ((mk_form (Fapp (eq,res :: z :: [])) tbool) :: ax) RN_ring g)

(**************************************************************************************************************)

let t_or_intro b g =
  let hyps, concl = get_goal g in
  let rec aux f =
    match f.f_node with
    | Fapp({f_node = Fop(p,_)}, [f1;f2]) when EcPath.p_equal p p_or ->
      let lem = if b then p_or_intro_l else p_or_intro_r in
      t_apply_logic lem [] [AAform f1; AAform f2; AAnode] g
    | Fapp({f_node = Fop(p,_)}, [f1;f2]) when EcPath.p_equal p p_ora ->
      let lem = if b then p_ora_intro_l else p_ora_intro_r in
      t_apply_logic lem [] [AAform f1; AAform f2; AAnode] g
    | _ ->
      match h_red_opt full_red hyps f with
      | Some f -> aux f
      | None ->
        let ppe = EcPrinting.PPEnv.ofenv (LDecl.toenv hyps) in
        tacuerror "Do not known how to split %a" (EcPrinting.pp_form ppe) f in
  aux concl

let t_left  = t_or_intro true
let t_right = t_or_intro false

let t_generalize_form ?fpat name f g =
  let fpat =
    match fpat with
    | None -> pattern_form name
    | Some fpat -> fpat
  in
  let hyps,concl = get_goal g in
  let x,body = fpat hyps f concl in
  let ff = f_forall [x,GTty f.f_ty] body in
  t_apply_form ff [AAform f] g

let t_generalize_hyps ids g =
  let hyps,concl = get_goal g in
  let env1 = LDecl.toenv hyps in
  let rec aux (s:f_subst) ids = 
    match ids with
    | [] -> Fsubst.f_subst s concl, [], []
    | id::ids ->
      match LDecl.ld_subst s (LDecl.lookup_by_id id hyps) with
      | LD_var (ty,body) ->
        let x = EcIdent.fresh id in
        let s = Fsubst.f_bind_local s id (f_local x ty) in
        let ff,args,lt = aux s ids in
        begin match body with
        | None -> 
          f_forall [x, GTty ty] ff, AAform (f_local id ty) :: args, lt
        | Some body ->
          f_let (LSymbol(x,ty)) body ff, args, lt
        end
      | LD_mem mt ->
        let x = EcIdent.fresh id in
        let s = Fsubst.f_bind_mem s id x in
        let ff, args, lt = aux s ids in
        f_forall [x, GTmem mt] ff, AAmem id :: args, lt
      | LD_modty (mt,r) -> 
        let x = EcIdent.fresh id in
        let s = Fsubst.f_bind_mod s id (EcPath.mident x) in
        let mp = EcPath.mident id in
        let sig_ = (EcEnv.Mod.by_mpath mp env1).EcModules.me_sig in
        let ff, args, lt = aux s ids in
        f_forall [x,GTmodty(mt,r)] ff, AAmp(mp,sig_) :: args, lt 
      | LD_hyp f ->
        let ff, args, lt = aux s ids in
        f_imp f ff, AAnode :: args, t_hyp id :: lt in
  let ff, args, lt = aux Fsubst.f_subst_id ids in
  t_seq_subgoal (t_apply_form ff args) (t_id None :: lt) g

let t_generalize_hyp id g = t_generalize_hyps [id] g

let t_generalize_hyps clear ids g = 
  if clear then 
    t_seq (t_generalize_hyps ids) (t_clear (EcIdent.Sid.of_list ids)) g
  else t_generalize_hyps ids g

(* -------------------------------------------------------------------- *)
let t_elimT tys p f sk g =
  let noelim () = tacuerror "not a valid elimination principle" in

  let (hyps, concl) = get_goal g in
  let env = LDecl.toenv hyps in
  let ax  = EcEnv.Ax.by_path p env in

  let rec skip i a f =
    match i, EcFol.sform_of_form f with
    | Some i, _ when i <= 0 -> (a, f)
    | Some i, SFimp (_, f2) -> skip (Some (i-1)) (AAnode :: a) f2
    | None  , SFimp (_, f2) -> skip None (AAnode :: a) f2
    | Some _, _ -> noelim ()
    | None  , _ -> (a, f)
  in

  match ax.EcDecl.ax_spec with
  | None -> noelim ()

  | Some _ ->
      let ax = EcEnv.Ax.instanciate p tys env in
      let (pr, prty, ax) =
        match sform_of_form ax with
        | SFquant (Lforall, (pr, GTty prty), ax) -> (pr, prty, ax)
        | _ -> noelim ()
      in

      if not (EcReduction.equal_type env prty (tfun f.f_ty tbool)) then
        noelim();

      let (aa1, ax) = skip None [] ax in

      let (x, _xty, ax) =
        match sform_of_form ax with
        | SFquant (Lforall, (x, GTty xty), ax) -> (x, xty, ax)
        | _ -> noelim ()
      in

      let (aa2, ax) =
        let rec doit ax aa =
          match destruct_product hyps ax with
          | Some (`Imp (f1, f2)) when Mid.mem pr f1.f_fv ->
              doit f2 (AAnode :: aa)
          | _ -> (aa, ax)
        in
          doit ax []
      in

      let pf =
        let (_, concl) = skip (Some sk) [] concl in
        let (z, concl) = pattern_form (Some (EcIdent.name x)) hyps f concl in
          Fsubst.f_subst_local pr (f_lambda [(z, GTty f.f_ty)] concl) ax
      in

      let pf_inst = Fsubst.f_subst_local x f pf in

      let (aa3, sk) =
        let rec doit pf_inst (aa, sk) =
          if   EcReduction.is_conv hyps pf_inst concl
          then (aa, sk)
          else
            match destruct_product hyps pf_inst with
            | Some (`Imp (_, f2)) -> doit f2 (AAnode :: aa, sk+1)
            | _ -> noelim ()
        in
          doit pf_inst ([], sk)
      in

      let pf = f_lambda [(x, GTty f.f_ty)] (snd (skip (Some sk) [] pf)) in
        t_apply_glob p tys (AAform pf :: aa1 @ (AAform f :: (aa2 @ aa3))) g

(* -------------------------------------------------------------------- *)
let t_case f g =
  check_logic (LDecl.toenv (get_hyps g)) p_case_eq_bool;
  t_elimT [] p_case_eq_bool f 0 g

let gen_t_exists do_arg fs (juc,n as g) =
  let hyps,concl = get_goal g in
  let rec aux s ras fs concl =
    match fs with
    | [] -> ras, (Fsubst.f_subst s concl)
    | f::fs' ->
      if is_exists concl then
        let (x,gty,concl) = destr_exists1 concl in
        let s, a = check_arg do_arg hyps s x gty f in
        aux s (a::ras) fs' concl
      else
        let concl = Fsubst.f_subst s concl in
        match h_red_opt full_red hyps concl with
        | Some f -> aux Fsubst.f_subst_id ras fs f
        | None -> 
          let ppe = EcPrinting.PPEnv.ofenv (LDecl.toenv hyps) in
          tacuerror "Do not known how to split %a" 
            (EcPrinting.pp_form ppe) concl in
  let args,concl = aux Fsubst.f_subst_id [] fs concl in
  let (juc,n1) = new_goal juc (hyps,concl) in
  let rule =
    {pr_name = RN_exists_intro; pr_hyps = List.rev_append args [RA_node n1] } in
  upd_rule rule (juc,n)

let t_exists = gen_t_exists (fun _ _ a -> a)

let t_split g =
  let hyps, concl = get_goal g in
  let env0 = LDecl.toenv hyps in
  let rec aux f =
    match f.f_node with
    | Fop(p,_) when EcPath.p_equal p p_true ->
      check_logic env0 p_true_intro;
      t_glob p_true_intro [] g
    | Fapp({f_node = Fop(p,_)}, [f1;f2]) ->
      begin
        match op_kind p with
        | OK_and b -> 
          t_apply_logic (if b then p_anda_intro else p_and_intro)
                [] [AAform f1;AAform f2;AAnode;AAnode] g
        | OK_iff   ->
          t_apply_logic p_iff_intro []
                [AAform f1;AAform f2;AAnode;AAnode] g
        | OK_eq when EcReduction.is_conv hyps f1 f2 -> t_reflex ~reduce:true g
        | OK_eq when is_tuple f1 && is_tuple f2 ->
          let fs1 = destr_tuple f1 in
          let fs2 = destr_tuple f2 in
          let types = List.map (fun v -> v.f_ty) fs1 in
          let args = List.map (fun f -> AAform f) (fs1@fs2) in
          let nodes = List.map (fun _ -> AAnode) fs1 in
          let lemma = gen_split_tuple_lemma types in
          let proof = gen_split_tuple_proof types in
          let gs = t_apply_form lemma (args@nodes) g in
          t_on_first proof gs
         | _ -> aux_red f
      end
    | Fif(f1,_f2,_f3) -> t_case f1 g
    | _ ->  aux_red f
  and aux_red f =
    match h_red_opt full_red hyps f with
    | Some f -> aux f
    | None -> 
      let ppe = EcPrinting.PPEnv.ofenv (LDecl.toenv hyps) in
      tacuerror "Do not known how to split %a"
        (EcPrinting.pp_form ppe) f in
  aux concl

let t_subst_gen x h side g =
  let hyps,concl = get_goal g in
  let f = LDecl.lookup_hyp_by_id h hyps in
  let hhyps,_,_ =
    List.find_split (fun (id, _) -> EcIdent.id_equal x id) (LDecl.tohyps hyps).h_local in
  let rec gen fv hhyps =
    match hhyps with
    | [] -> ([], [], concl)
    | (id, lk) :: hhyps ->
      if EcIdent.id_equal id h then gen fv hhyps
      else match lk with
      | LD_var (ty, Some body) when not (Mid.set_disjoint body.f_fv fv) ->
        let aa, ids, concl = gen (Sid.add id fv) hhyps in
        aa, id::ids, f_let (LSymbol(id,ty)) body concl
      | LD_hyp f when not (Mid.set_disjoint f.f_fv fv) ->
        let aa, ids, concl = gen fv hhyps in
        id::aa, id::ids, f_imp f concl
      | _ -> gen fv hhyps in
  let aa, ids, concl = gen (Sid.singleton x) hhyps in
  let t_first =
    t_seq_subgoal (t_rewrite side f)
      [ t_hyp h;
        t_seq (t_clear (Sid.of_list (x::h::ids))) (t_intros_i ids) ] in
  t_seq_subgoal (t_apply_form concl (List.map (fun _ -> AAnode) aa))
    (t_first :: List.map t_hyp aa) g

let cansubst_eq hyps x f1 f2 = 
  match f1.f_node, x with
  | Flocal id, Some x when EcIdent.id_equal id x ->
    let f2 = simplify {no_red with delta_h = None} hyps f2 in
    if Mid.mem id f2.f_fv then None else Some id
  | Flocal id, None ->
    let f2 = simplify {no_red with delta_h = None} hyps f2 in
    if Mid.mem id f2.f_fv then None else Some id
  | _         -> None

let is_subst_eq hyps x (hid,lk) =
  match lk with
  | LD_hyp f ->
    if is_eq_or_iff f then
      let f1, f2 = destr_eq_or_iff f in
      match cansubst_eq hyps x f1 f2 with
      | Some id -> Some(hid, id,`LtoR)
      | None ->
        match cansubst_eq hyps x f2 f1 with
        | Some id -> Some(hid, id,`RtoL)
        | None -> None
    else None
  | _ -> None

let t_subst1_loc x g =
  let hyps = get_hyps g in
  match List.pick (is_subst_eq hyps x) (LDecl.tohyps hyps).h_local with
  | None -> 
    begin match x with
    | None -> tacuerror "Cannot find non recursive equation to substitute"
    | Some id -> 
      tacuerror "Cannot find non recursive equation on %s" (EcIdent.name id)
    end
  | Some(h, x, side) ->
      t_subst_gen x h side g

(* Substitution of f1 = Fpvar(pv,m) | Fglob(mp,m) *)

let pattern_pv hyps f1 f =
  let x = EcIdent.create "x" in
  let fx = EcFol.f_local x f1.f_ty in
  let env = LDecl.toenv hyps in
  let f1 = EcEnv.NormMp.norm_form env f1 in
  let subst = 
    match f1.f_node with
    | Fpvar (pv,m) -> EcPV.PVM.add env pv m fx EcPV.PVM.empty 
    | Fglob (mp,m) -> EcPV.PVM.add_glob env mp m fx EcPV.PVM.empty
    | _ -> assert false in
  let body = EcPV.PVM.subst env subst f in
  x, body

let t_subst_pv_gen h side g =
  let hyps,_ = get_goal g in
  let f = LDecl.lookup_hyp_by_id h hyps in
  let to_gen = 
    List.filter (fun (id,lk) ->
      match lk with
      | LD_hyp _ -> not (EcIdent.id_equal h id) 
      | LD_var (_, Some _) -> true
      | _ -> false) (List.rev (LDecl.tohyps hyps).h_local) in
  let to_gen = List.map fst to_gen in
  let to_intros =
    List.map (fun id -> { pl_loc = EcLocation._dummy; pl_desc = id }) to_gen in
  t_seq (t_generalize_hyps true to_gen)
    (t_seq_subgoal (t_rewrite_gen pattern_pv side f)
            [t_hyp h; 
             t_seq (t_clear (EcIdent.Sid.singleton h))
               (t_intros to_intros)]) g

let cansubst_pv_eq hyps fx f1 f2 = 
  let env = (LDecl.toenv hyps) in
  let testfx f1 = 
    match fx with
    | None -> true
    | Some fx -> f_equal f1 (EcEnv.NormMp.norm_form env fx) in
  let check f1 = 
    let f1' = EcEnv.NormMp.norm_form env f1 in
    if testfx f1' then
      match f1'.f_node with
      | Fpvar(pv,m) ->
        let f2 = simplify {no_red with delta_h = None} hyps f2 in
        let fv = EcPV.PV.fv env m f2 in
        if EcPV.PV.mem_pv env pv fv then None
        else Some f1'
      | Fglob(mp,m) -> 
        let f2 = simplify {no_red with delta_h = None} hyps f2 in
        let fv = EcPV.PV.fv env m f2 in
        if EcPV.PV.mem_glob env mp fv then None
        else Some f1'
      | _ -> None
    else None in
  match f1.f_node with
  | Fpvar _ | Fglob _ -> check f1
  | _ -> None 

let is_subst_pv_eq hyps fx (hid,lk) =
  match lk with
  | LD_hyp f ->
    if is_eq_or_iff f then
      let f1, f2 = destr_eq_or_iff f in
      match cansubst_pv_eq hyps fx f1 f2 with
      | Some id -> Some(hid, id,`LtoR)
      | None ->
        match cansubst_pv_eq hyps fx f2 f1 with
        | Some id -> Some(hid, id,`RtoL)
        | None -> None
    else None
  | _ -> None

let t_subst1_pv fx g =
  let hyps = get_hyps g in
  let rec aux local = 
    match local with 
    | [] -> tacuerror "cannot find something to subst"
    | h :: l ->
      match is_subst_pv_eq hyps fx h with
      | Some(h, _x, side) ->
        (try t_subst_pv_gen h side g with EcPV.MemoryClash -> aux l)
      | _ -> aux l in
  aux (LDecl.tohyps hyps).h_local 

let t_subst1 fx g = 
  match fx with
  | None -> t_or (t_subst1_loc None) (t_subst1_pv None) g
  | Some fx ->
    match fx.f_node with
    | Flocal id -> t_subst1_loc (Some id) g
    | (Fpvar _ | Fglob _) -> t_subst1_pv (Some fx) g
    | _ -> tacuerror "subst1"           (* FIXME: error message *)

let t_subst_all =
  t_repeat (t_subst1 None)

let find_in_hyps f hyps =
  let test k =
    try
      let _, f' = LDecl.get_hyp k in
      check_conv hyps f f'; true
    with _ -> false in
  fst (List.find test (LDecl.tohyps hyps).h_local)

let t_assumption g = 
  let (hyps, concl) = get_goal g in
  let myh =
    try  find_in_hyps concl hyps
    with Not_found -> tacuerror "no assumption"
  in
    t_hyp myh g
    
let t_progress tac g =
  let rec aux g = t_seq t_simplify_nodelta aux0 g 
  and aux0 g =
    t_seq (t_try tac) aux1 g
  and aux1 g = 
    let hyps,concl = get_goal g in
    match concl.f_node with
    | Fquant(Lforall,bd,_) ->
      let ids = 
        LDecl.fresh_ids hyps (List.map (fun (id,_) -> EcIdent.name id) bd) in
      t_seq (t_intros_i ids) aux g
    | Flet (LTuple fs,f1,_) ->
      let p = p_tuple_ind (List.length fs) in
      t_seq (t_elimT (List.map snd fs) p f1 0) aux g
    | Fapp({f_node = Fop(p,_)}, [f1;_]) when EcPath.p_equal p EcCoreLib.p_imp ->
      let id = LDecl.fresh_id hyps "H" in
      t_seq (t_intros_i [id]) (aux2 id f1) g
    | _ -> t_try (t_seq t_split aux) g
  and aux2 id f g = 
    let t1 = 
      match f.f_node with
      | Fop(p,_) when EcPath.p_equal p p_false -> t_elim_hyp id
      | Fapp({f_node = Fop(p,_)}, [_;_] ) when is_op_and p -> 
        t_seq (t_elim_hyp id) (t_clear (Sid.singleton id)) 
      | Fquant(Lexists,_,_) -> 
        t_seq (t_elim_hyp id) (t_clear (Sid.singleton id))
      | _ when is_eq f -> 
        let f1, f2 = destr_eq f in
        if is_tuple f1 && is_tuple f2 then 
          t_seq (t_elim_hyp id) (t_clear (Sid.singleton id))
        else t_subst_all 
          
      | _ -> t_subst_all (* FIXME should allows to subst a given hyps *) in
    t_seq t1 aux g in
  aux g

(* -------------------------------------------------------------------- *)
let t_congr f (args, ty) g =
  let rec doit args ty g =
    match args with
    | [] -> t_reflex g

    | (a1, a2) :: args->
        let aty  = a1.f_ty in
        let m1   = f_app f (List.rev_map fst args) (tfun aty ty) in
        let m2   = f_app f (List.rev_map snd args) (tfun aty ty) in
        let tcgr = t_apply_logic EcCoreLib.p_fcongr
                     [ty; aty]
                     [AAform m1; AAform a1; AAform a2; AAnode] in

        let tsub g =
          let fx   = EcIdent.create "f" in
          let fty  = tfun aty ty in
          let body = f_app (f_local fx fty) [a2] ty in
          let lam  = EcFol.f_lambda [(fx, GTty fty)] body in
            t_subgoal
              [doit args fty]
              (t_apply_logic EcCoreLib.p_fcongr
                 [ty; fty]
                 [AAform lam; AAform m1; AAform m2; AAnode] g)
        in
          t_subgoal
            [tcgr; tsub]
            (t_transitivity (EcFol.f_app m1 [a2] ty) g)
  in
    t_on_goals (t_try t_assumption) (doit (List.rev args) ty g)


(* -------------------------------------------------------------------- *)
let t_trivial =
  t_or
    (t_lseq [t_try t_assumption; t_progress (t_id None); t_assumption; t_fail])
    (t_id None)
