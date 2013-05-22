(* -------------------------------------------------------------------- *)
open EcLocation
open EcUtils
open EcSymbols
open EcIdent
open EcPath
open EcCoreLib
open EcTypes
open EcFol
open EcBaseLogic
open EcEnv
open EcReduction

(* -------------------------------------------------------------------- *)
let get_node  g = (get_goal g).pj_decl
let get_goal  g = (get_open_goal g).pj_decl
let get_hyps  g = fst (get_goal g)
let get_concl g = snd (get_goal g)

(* -------------------------------------------------------------------- *)
type tac_error =
  | UnknownAx             of EcPath.path
  | NotAHypothesis        of EcIdent.t
  | UnknownElims          of form
  | UnknownIntros         of form
  | UnknownSplit          of form
  | UnknownRewrite        of form
  | LogicRequired
  | CannotClearConcl      of EcIdent.t * form
  | CannotReconizeElimT
  | TooManyArgument
  | NoHypToSubst          of EcIdent.t option
  | CannotProve           of l_decl
  | InvalNumOfTactic      of int * int
  | NotPhl                of bool option
  | NoSkipStmt
  | InvalidCodePosition   of string*int*int*int
  | CanNotApply           of string * string
  | InvalidName           of string
  | User                  of string

exception TacError of tac_error

let pp_tac_error fmt error =
  let env = EcEnv.initial in            (* FIXME *)
  match error with
  | UnknownAx p ->
      Format.fprintf fmt "Unknown axiom/lemma %a" PE.pp_path p
  | NotAHypothesis id ->
      Format.fprintf fmt "Unknown hypothesis %s" (EcIdent.name id)
  | UnknownElims f ->
    Format.fprintf fmt "Do not known what to eliminate in %a" (PE.pp_form env) f
  | UnknownIntros f ->
    Format.fprintf fmt "Do not known what to introduce in %a" (PE.pp_form env) f
  | UnknownSplit f ->
    Format.fprintf fmt "Do not known how to split %a" (PE.pp_form env) f
  | UnknownRewrite f ->
    Format.fprintf fmt "Do not known how to rewrite %a" (PE.pp_form env) f
  | LogicRequired ->
    Format.fprintf fmt "Require import Logic first"
  | CannotClearConcl(id,_) ->
    Format.fprintf fmt "Cannot clear %s, it is used in the conclusion"
      (EcIdent.name id)
  | CannotReconizeElimT ->
    Format.fprintf fmt "Cannot reconize the elimination lemma"
  | TooManyArgument ->
    Format.fprintf fmt "Too many arguments in the application"
  | NoHypToSubst (Some id) ->
    Format.fprintf fmt "Cannot find non recursive equation on %s"
      (EcIdent.name id)
  | NoHypToSubst None ->
    Format.fprintf fmt "Cannot find non recursive equation to substitute"
  | CannotProve _ ->
    Format.fprintf fmt "Cannot prove current goal"
  | InvalNumOfTactic (i1,i2) ->
    Format.fprintf fmt "Invalid number of tactics: %i given, %i expected" i2 i1
  | NoSkipStmt ->
    Format.fprintf fmt "Cannot apply skip rule"
  | NotPhl b ->
    let s =
      match b with
      | None -> "phl/prhl"
      | Some true -> "phl"
      | Some false -> "prhl" in
    Format.fprintf fmt "The conclusion does not end by a %s judgment" s
  | InvalidCodePosition (msg,k,lb,up) ->
    Format.fprintf fmt "%s: Invalid code line number %i, expected in [%i,%i]" msg k lb up
  | CanNotApply(s1,s2) ->
    Format.fprintf fmt "Can not apply %s tactic:@\n %s" s1 s2
  | InvalidName x ->
    Format.fprintf fmt "Invalid name for this kind of object: %s" x
  | User msg ->
    Format.fprintf fmt "%s" msg

let _ = EcPException.register (fun fmt exn ->
  match exn with
  | TacError error -> pp_tac_error fmt error
  | _ -> raise exn)

let tacerror error = raise (TacError error)

let tacuerror fmt =
  Printf.ksprintf
    (fun msg -> raise (TacError (User msg)))
    fmt

let cannot_apply s1 s2 = tacerror (CanNotApply(s1,s2))

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
let use_node env juc n n1 =
  let hyps,concl = get_node (juc,n) in
  let hyps',concl' = get_goal (juc,n1) in
  check_hyps hyps hyps';
  check_conv env hyps concl concl';
  let rule = { pr_name = RN_conv; pr_hyps = [RA_node n] } in
  fst (upd_rule rule (juc,n1))

let t_use env n gs (juc,n1) =
  use_node env juc n n1, gs

let t_change env f (juc,n1) =
  let hyps = get_hyps (juc,n1) in
  check_type env f.f_ty tbool;
  let (juc,n) = new_goal juc (hyps,f) in
  t_use env n [n] (juc,n1)

let t_red env g =
  let hyps, concl = get_goal g in
  let f = EcReduction.h_red EcReduction.full_red env hyps concl in
  t_change env f g

let t_simplify env ri (juc,n1 as g) =
  let hyps, concl = get_goal g in
  let f = EcReduction.simplify ri env hyps concl in
  let (juc,n) = new_goal juc (hyps,f) in
  let rule = { pr_name = RN_conv; pr_hyps = [RA_node n] } in
  upd_rule rule (juc,n1)

let mkn_hyp juc hyps id =
  let f = LDecl.lookup_hyp_by_id id hyps in
  let juc,n = new_goal juc (hyps,f) in
  let rule = { pr_name = RN_hyp id; pr_hyps = [] } in
  let juc, _ = upd_rule_done rule (juc,n) in
  juc, n

let t_hyp env id (juc,n as g) =
  let hyps = get_hyps g in
  let juc,nh = mkn_hyp juc hyps id in
  use_node env juc nh n, []

let mkn_glob env juc hyps p tys =
  let f = Ax.instanciate p tys env in
  let juc, n = new_goal juc (hyps,f) in
  let rule = { pr_name = RN_glob(p,tys); pr_hyps = [] } in
  let juc, _ = upd_rule_done rule (juc, n) in
  juc, n

let t_glob env p tys (juc,n as g) =
  let hyps = get_hyps g in
  let juc, nh = mkn_glob env juc hyps p tys in
  use_node env juc nh n, []

let t_trivial pi env g =
  let goal = get_goal g in
  if EcEnv.check_goal env pi goal then
    let rule = { pr_name = RN_prover (); pr_hyps = [] } in
    upd_rule_done rule g
  else tacerror (CannotProve goal)

let t_clear ids (juc,n as g) =
  let hyps,concl = get_goal g in
  if not (Mid.set_disjoint ids concl.f_fv) then
    tacerror (CannotClearConcl(Sid.choose (Mid.set_inter ids concl.f_fv), concl));
  let hyps = LDecl.clear ids hyps in
  let juc,n1 = new_goal juc (hyps,concl) in
  let rule = { pr_name = RN_clear ids; pr_hyps = [RA_node n1] } in
  upd_rule rule (juc,n)

let tyenv_of_hyps env hyps =
  let add env (id,k) =
    match k with
    | LD_var (ty,_) -> EcEnv.Var.bind_local id ty env
    | LD_mem mt     -> EcEnv.Memory.push (id,mt) env
    | LD_modty (i,r)    -> EcEnv.Mod.bind_local id i r env
    | LD_hyp   _    -> env in
  List.fold_left add env hyps.h_local

let check_modtype _env _mp _i _restr = ()
 (* TODO FIXME *)
(*
  let me = EcEnv.Mod.by_mpath mp in
  if not (EcEnv.ModTy.has_mod_type env me.me_types) then
    assert false (* FIXME error message *);
  let use = top_uses mp in
  let 
*)  
  

  

type app_arg =
  | AAform of form
  | AAmem  of EcIdent.t
  | AAmp   of EcPath.mpath
  | AAnode

let check_arg do_arg env hyps s x gty a =
  let a = do_arg env hyps (Some gty) a in
  match gty, a with
  | GTty ty  , AAform f ->
    check_type env ty f.f_ty; (* FIXME error message *)
    bind_local s x f, RA_form f
  | GTmem _   , AAmem m ->
    bind_mem s x m, RA_id m
  | GTmodty (i,restr), AAmp mp  ->
      (* FIXME : check the type of mp *)
    let env = tyenv_of_hyps env hyps in
    check_modtype env mp i restr;
    bind_mod s x mp, RA_mp mp
  | _ -> assert false (* FIXME error message *)

let mkn_apply do_arg env (juc,n) args =
  if args = [] then (juc,n), []
  else
    let hyps,concl = get_node (juc,n) in
    let check_arg = check_arg do_arg env hyps in
    let rec check_apply juc s ras f args =
      match args with
      | [] -> juc, List.rev ras, f_subst s f
      | a :: args' ->
        if is_forall f then 
          let (x,gty,f') = destr_forall1 f in
          let s, ra = check_arg s x gty a in
          check_apply juc s (ra::ras) f' args' 
        else if is_imp f then 
          let (f1,f2) = destr_imp f in
          let a = do_arg env hyps None a in
          assert (a = AAnode); (* FIXME error message *)
          let juc, n = new_goal juc (hyps, f_subst s f1) in
          check_apply juc s (RA_node n :: ras) f2 args' 
        else 
          let f = f_subst s f in
          match h_red_opt full_red env hyps f with
          | None -> tacerror TooManyArgument
          | Some f ->  check_apply juc f_subst_id ras f args in
    let juc, ras, concl = check_apply juc f_subst_id [] concl args in
    let (juc,n1) = new_goal juc (hyps,concl) in
    let rule = { pr_name = RN_apply; pr_hyps = RA_node n :: ras} in
    let juc, _ = upd_rule rule (juc,n1) in
    let ns = List.pmap (function RA_node n -> Some n | _ -> None) ras in
    (juc,n1), ns

let gen_t_apply do_arg env fn args (juc,n) =
  let (juc,an), ns = mkn_apply do_arg env (juc,fn) args in
  (use_node env juc an n, ns)

let gen_t_apply_form do_arg env f args (juc, n as g) =
  let hyps = get_hyps g in
  let juc, fn = new_goal juc (hyps, f) in
  let juc,ns = gen_t_apply do_arg env fn args (juc,n) in
  juc, fn::ns

let t_apply_form = gen_t_apply_form (fun _ _ _ a -> a)

let gen_t_apply_glob do_arg env p tys args (juc,n as g) =
  let hyps = get_hyps g in
  let juc,fn = mkn_glob env juc hyps p tys in
  gen_t_apply do_arg env fn args (juc,n)

let t_apply_glob = gen_t_apply_glob (fun _ _ _ a -> a)

let gen_t_apply_hyp do_arg env id args (juc ,n as g) =
  let hyps = get_hyps g in
  let juc,fn = mkn_hyp juc hyps id in
  gen_t_apply do_arg env fn args (juc, n)

let t_apply_hyp = gen_t_apply_hyp (fun _ _ _ a -> a)

let check_logic env p =
  try ignore (EcEnv.Ax.by_path p env) with _ ->
    tacerror LogicRequired

let t_apply_logic env p tyargs args g =
  check_logic env p;
  t_apply_glob env p tyargs args g

let t_cut env f g =
  let concl = get_concl g in
  t_apply_logic env p_cut_lemma [] [AAform f;AAform concl;AAnode;AAnode] g

let set_loc loc f x =
  try f x
  with e -> EcLocation.locate_error loc e

let t_intros env ids (juc,n as g) =
  let hyps, concl = get_goal g in
  let add_local s id x gty =
    let id   = id.pl_desc in
    let name = EcIdent.name id in
    match gty with
    | GTty ty ->
        if name <> "_" && not (EcIo.is_sym_ident name) then
          tacerror (InvalidName name);
        LD_var(ty,None), bind_local s x (f_local id ty)

    | GTmem me ->
        if name <> "_" && not (EcIo.is_mem_ident name) then
          tacerror (InvalidName name);
        LD_mem me, bind_mem s x id

    | GTmodty (i,r) ->
        if name <> "_" && not (EcIo.is_mod_ident name) then
          tacerror (InvalidName name);
        LD_modty (i,r), bind_mod s x (EcPath.mident id)
  in

  let add_ld id ld hyps =
    set_loc id.pl_loc (LDecl.add_local id.pl_desc ld) hyps in

  let rec check_intros hyps ids s concl =
    match ids with
    | [] -> hyps, f_subst s concl
    | id::ids' ->
      if is_forall concl then
        let (x,gty,concl) = destr_forall1 concl in
        let ld, s = add_local s id x gty in
        let hyps = add_ld id ld hyps in
        check_intros hyps ids' s concl
      else if is_imp concl then
        let f1, f2 = destr_imp concl in
        let hyps = add_ld id (LD_hyp (f_subst s f1)) hyps in
        check_intros hyps ids' s f2
      else if is_let1 concl then
        let x,ty,e1,concl = destr_let1 concl in
        let s = bind_local s x (f_local id.pl_desc ty) in
        let hyps = add_ld id (LD_var (ty, Some (f_subst s e1))) hyps in
        check_intros hyps ids' s concl
      else if s == f_subst_id then
        match h_red_opt full_red env hyps concl with
        | None -> tacerror (UnknownIntros concl)
        | Some concl -> check_intros hyps ids s concl
      else check_intros hyps ids f_subst_id (f_subst s concl) in
  let hyps, concl = check_intros hyps ids f_subst_id concl in
  let (juc,n1) = new_goal juc (hyps,concl) in
  let ids = List.map unloc ids in
  let rule = { pr_name = RN_intros ids; pr_hyps = [RA_node n1]} in
  upd_rule rule (juc,n)

(* internal use *)
let t_intros_i env ids g =
  t_intros env
    (List.map (fun id -> {pl_desc = id; pl_loc = EcLocation._dummy}) ids)
    g

let t_elim env f (juc,n) =
  let hyps,concl = get_goal (juc,n) in
  let rec aux f =
    match f.f_node with
    | Fop(p,_) when EcPath.p_equal p p_false ->
      t_apply_logic env p_false_elim [] [AAform concl; AAnode] (juc,n)

    | Fapp({f_node = Fop(p,_)}, [a1;a2] ) ->
      let lem =
        match op_kind p with
        | OK_and b ->
          Some ((if b then p_anda_elim else p_and_elim),[AAnode;AAnode])
        | OK_or b  ->
          Some ((if b then p_ora_elim else p_or_elim),[AAnode;AAnode;AAnode])
        | OK_iff   -> Some (p_iff_elim,[AAnode;AAnode])
        | _        -> None in
      begin match lem with
      | Some (p,a) ->
        t_apply_logic env p [] ([AAform a1;AAform a2;AAform concl]@a) (juc,n)
      | None -> aux_red f
      end
    | Fif(a1,a2,a3) ->
      t_apply_logic env p_if_elim [] [AAform a1;AAform a2;AAform a3;
                                     AAform concl;AAnode;AAnode;AAnode] (juc,n)
    | Fquant(Lexists,bd,f') ->
      let juc,n1 = new_goal juc (hyps, f) in
      let juc,n2 = new_goal juc (hyps,f_forall bd (f_imp f' concl)) in
      let rule = { pr_name = RN_exists_elim; pr_hyps = [RA_node n1; RA_node n2] } in
      upd_rule rule (juc, n)
    | _ -> aux_red f

  and aux_red f =
    match h_red_opt full_red env hyps f with
    | Some f -> aux f
    | _ -> tacerror (UnknownElims f) in
  aux f

let t_elim_hyp env h g =
  let f = LDecl.lookup_hyp_by_id h (get_hyps g) in
  t_on_first (t_elim env f g) (t_hyp env h)

let t_split env g =
  let hyps, concl = get_goal g in
  let rec aux f =
    match f.f_node with
    | Fop(p,_) when EcPath.p_equal p p_true ->
      check_logic env p_true_intro;
      t_glob env p_true_intro [] g
    | Fapp({f_node = Fop(p,_)}, [f1;f2]) ->
      let lem =
        match op_kind p with
        | OK_and b ->
          Some ((if b then p_anda_intro else p_and_intro),
                [], [AAform f1;AAform f2;AAnode;AAnode])
        | OK_iff   -> Some (p_iff_intro, [], [AAform f1;AAform f2;AAnode;AAnode])
        | OK_eq    -> Some (p_eq_refl, [f1.f_ty], [AAform f1])
        | _        -> None in
      begin match lem with
      | Some (p,tys,aa) -> t_apply_logic env p tys aa g
      | None -> aux_red f
      end
    | Fif(f1,f2,f3) ->
      t_apply_logic env p_if_intro []
        [AAform f1; AAform f2; AAform f3;AAnode;AAnode] g
    | _ ->  aux_red f
  and aux_red f =
    match h_red_opt full_red env hyps f with
    | Some f -> aux f
    | None -> tacerror (UnknownSplit f) in
  aux concl

let t_or_intro b env g =
  let hyps, concl = get_goal g in
  let rec aux f =
    match f.f_node with
    | Fapp({f_node = Fop(p,_)}, [f1;f2]) when EcPath.p_equal p p_or ->
      let lem = if b then p_or_intro_l else p_or_intro_r in
      t_apply_logic env lem [] [AAform f1; AAform f2; AAnode] g
    | Fapp({f_node = Fop(p,_)}, [f1;f2]) when EcPath.p_equal p p_ora ->
      let lem = if b then p_ora_intro_l else p_ora_intro_r in
      t_apply_logic env lem [] [AAform f1; AAform f2; AAnode] g
    | _ ->
      match h_red_opt full_red env hyps f with
      | Some f -> aux f
      | None -> tacerror (UnknownSplit f) in
  aux concl

let t_left  = t_or_intro true
let t_right = t_or_intro false

let pattern_form name env hyps f1 f =
  let x = EcIdent.create (odfl "x" name) in
  let fx = EcFol.f_local x f1.f_ty in
  let body =
    Hf.memo_rec 107
      (fun aux f ->
        if EcReduction.is_alpha_eq env hyps f f1 then fx
        else f_map (fun ty -> ty) aux f)
      f in
  x, body

let t_generalize_form name env f g =
  let hyps,concl = get_goal g in
  let x,body = pattern_form name env hyps f concl in
  let ff = f_forall [x,GTty f.f_ty] body in
  t_apply_form env ff [AAform f] g

let t_generalize_hyp env id g =
  let hyps,concl = get_goal g in
  match LDecl.lookup_by_id id hyps with
  | LD_var (ty,_) ->
    t_generalize_form (Some (EcIdent.name id)) env (f_local id ty) g
  | LD_mem mt ->
    let x = EcIdent.fresh id in
    let s = EcFol.bind_mem f_subst_id id x in
    let body = f_subst s concl in
    let ff = f_forall [x, GTmem mt] body in
    t_apply_form env ff [AAmem id] g
  | LD_modty _ -> assert false (* Not implemented *)
  | LD_hyp f ->
    t_on_last (t_apply_form env (f_imp f concl) [AAnode] g) (t_hyp env id)

let gen_t_exists do_arg env fs (juc,n as g) =
  let hyps,concl = get_goal g in
  let rec aux s ras fs concl =
    match fs with
    | [] -> ras, (f_subst s concl)
    | f::fs' ->
      if is_exists concl then
        let (x,gty,concl) = destr_exists1 concl in
        let s, a = check_arg do_arg env hyps s x gty f in
        aux s (a::ras) fs' concl
      else
        let concl = f_subst s concl in
        match h_red_opt full_red env hyps concl with
        | Some f -> aux f_subst_id ras fs f
        | None -> tacerror (UnknownSplit concl) in
  let args,concl = aux f_subst_id [] fs concl in
  let (juc,n1) = new_goal juc (hyps,concl) in
  let rule =
    {pr_name = RN_exists_intro; pr_hyps = List.rev_append args [RA_node n1] } in
  upd_rule rule (juc,n)

let t_exists = gen_t_exists (fun _ _ _ a -> a)

let t_rewrite env side f g =
  let hyps,concl = get_goal g in
  let rec find_rewrite f =
    if is_eq f then destr_eq f, true
    else if is_iff f then destr_iff f, false
    else
      match h_red_opt full_red env hyps f with
      | Some f -> find_rewrite f
      | None   -> tacerror (UnknownRewrite f) in
  let (f1,f2),eq = find_rewrite f in
  let p,tys =
    if eq then (if side then p_rewrite_l else p_rewrite_r), [f1.f_ty]
    else (if side then p_rewrite_iff_l else p_rewrite_iff_r), [] in
  let pred =
    let f = if side then f1 else f2 in
    let x, body = pattern_form None env hyps f concl in
    f_lambda [x,GTty f.f_ty] body in
  t_on_last
    (t_apply_logic env p tys [AAform f1;AAform f2;AAform pred;AAnode;AAnode] g)
    (t_red env)

let t_rewrite_node env ((juc,an), gs) side n =
  let (_,f) = get_node (juc, an) in
  t_seq_subgoal (t_rewrite env side f)
    [t_use env an gs;t_id] (juc,n)

let t_rewrite_hyp env side id args (juc,n as g) =
  let hyps = get_hyps g in
  let g' = mkn_hyp juc hyps id in
  t_rewrite_node env (mkn_apply (fun _ _ _ a -> a) env g' args) side n

let t_elimT env f p g =
  let hyps,concl = get_goal g in
  let ax = EcEnv.Ax.by_path p env in
  let rec skip_imp a f =
    if is_imp f then skip_imp (AAnode::a) (snd (destr_imp f))
    else a, f in

  match ax.EcDecl.ax_spec with
  | None -> tacerror (CannotReconizeElimT)
  | Some fax ->
    let tys =
      let tpred =
        try
          match destr_forall1 fax with
          | _, GTty ty, _ -> ty
          | _             -> raise Not_found
        with _ -> tacerror (CannotReconizeElimT) in
      let ue = EcUnify.UniEnv.create (Some hyps.h_tvar) in
      let (ue, tpred,tys) =
        EcUnify.UniEnv.freshen ue ax.EcDecl.ax_tparams None tpred in
      EcUnify.unify env ue tpred (tfun f.f_ty tbool);
      let subst = Tuni.subst (EcUnify.UniEnv.close ue) in
      List.map subst tys in
    let fax = EcEnv.Ax.instanciate p tys env in
    let vx, _, fax = destr_forall1 fax in
    let pf =
      let x, body = pattern_form (Some (EcIdent.name vx)) env hyps f concl in
      f_lambda [x,GTty f.f_ty] body in
    let aa =
      if is_forall fax then
        let _,_,fax = destr_forall1 fax in
        let aa, _ = skip_imp [] fax in
        AAform f::aa
      else
        let aa,fax = skip_imp [] fax in
        if not (is_forall fax) then tacerror (CannotReconizeElimT);
        List.rev_append aa [AAform f] in
    t_apply_glob env p tys (AAform pf::aa) g

let t_case env f g =
  check_logic env p_case_eq_bool;
  t_elimT env f p_case_eq_bool g

let t_subst_gen env x h side g =
  let hyps,concl = get_goal g in
  let f = LDecl.lookup_hyp_by_id h hyps in
  let hhyps,_,_ =
    List.find_split (fun (id, _) -> EcIdent.id_equal x id) hyps.h_local in
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
  let tointros =
    List.map (fun id -> { pl_loc = EcLocation._dummy; pl_desc = id }) ids in
  let t_first =
    t_seq_subgoal (t_rewrite env side f)
      [ t_hyp env h;
        t_seq (t_clear (Sid.of_list (x::h::ids))) (t_intros env tointros) ] in
  t_seq_subgoal (t_apply_form env concl (List.map (fun _ -> AAnode) aa))
    (t_first :: List.map (t_hyp env) aa) g

let cansubst_eq env hyps x f1 f2 =
  match f1.f_node, x with
  | Flocal id, Some x when EcIdent.id_equal id x ->
    let f2 = simplify {no_red with delta_h = None} env hyps f2 in
    if Mid.mem id f2.f_fv then None else Some id
  | Flocal id, None ->
    let f2 = simplify {no_red with delta_h = None} env hyps f2 in
    if Mid.mem id f2.f_fv then None else Some id
  | _         -> None

let is_subst_eq env hyps x (hid,lk) =
  match lk with
  | LD_hyp f ->
    if is_eq f then
      let f1, f2 = destr_eq f in
      match cansubst_eq env hyps x f1 f2 with
      | Some id -> Some(hid, id,true)
      | None ->
        match cansubst_eq env hyps x f2 f1 with
        | Some id -> Some(hid, id,false)
        | None -> None
    else None
  | _ -> None

let t_subst1 env x g =
  let hyps = get_hyps g in
  match List.pick (is_subst_eq env hyps x) hyps.h_local with
  | None -> tacerror (NoHypToSubst x)
  | Some(h, x, side) ->
    t_subst_gen env x h side g

let t_subst_all env =
  t_repeat (t_subst1 env None)

let find_in_hyps env f hyps =
  let test k =
    try
      let _, f' = LDecl.get_hyp k in
      check_conv env hyps f f'; true
    with _ -> false in
  fst (List.find test hyps.h_local)
